# -*- coding: utf-8 -*-
"""
Photo Uploader for Papu.io
Automated dish photo uploader based on dish names matching image files.
"""

import os
import sys

# Bezpieczne przekierowanie dla PyInstallera w trybie bez konsoli (--noconsole)
if sys.stdout is None:
    sys.stdout = open(os.devnull, "w", encoding="utf-8")
if sys.stderr is None:
    sys.stderr = open(os.devnull, "w", encoding="utf-8")

import time
import json
import re
import unicodedata
import threading
import tempfile
import tkinter as tk
from tkinter import filedialog, messagebox, ttk
from datetime import datetime

# External dependencies
from selenium import webdriver
from selenium.webdriver.chrome.service import Service
from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from webdriver_manager.chrome import ChromeDriverManager
from PIL import Image

VERSION = "1.3 by ErykNowicki"

# ==============================================================================
# STRING & IMAGE NORMALIZATION / MATCHING
# ==============================================================================

DIACRITICS_MAP = {
    'ą': 'a', 'ć': 'c', 'ę': 'e', 'ł': 'l', 'ń': 'n',
    'ó': 'o', 'ś': 's', 'ź': 'z', 'ż': 'z',
    'Ą': 'A', 'Ć': 'C', 'Ę': 'E', 'Ł': 'L', 'Ń': 'N',
    'Ó': 'O', 'Ś': 'S', 'Ź': 'Z', 'Ż': 'Z'
}


def strip_diacritics(text: str) -> str:
    """Zamienia polskie znaki diakrytyczne na odpowiedniki ASCII."""
    for pl, asc in DIACRITICS_MAP.items():
        text = text.replace(pl, asc)
    return text


def norm_text(s: str) -> str:
    """Normalizuje tekst: NFKC, jednolite spacje, myślniki, strip, casefold."""
    if not s:
        return ""
    t = unicodedata.normalize("NFKC", str(s))
    t = t.replace("\xa0", " ")
    t = re.sub(r"[\u2010\u2011\u2012\u2013\u2014\u2212]", "-", t)
    t = re.sub(r"[\u200b\u200c\u200d\u2060]", "", t)
    t = re.sub(r"\s+", " ", t).strip()
    return t.casefold()


class ImageMatcher:
    """
    Indeksuje zdjęcia z katalogu i dopasowuje je do nazw dań.
    Obsługuje również automatyczną konwersję .webp -> .png.
    """

    ALLOWED_EXTENSIONS = {'.png', '.jpg', '.jpeg', '.webp', '.gif', '.jfif'}

    def __init__(self, folder_path: str, auto_convert_webp: bool = True, log_func=print):
        self.folder_path = folder_path
        self.auto_convert_webp = auto_convert_webp
        self.log_func = log_func
        self.cache_dir = os.path.join(folder_path, ".cache_converted")
        self.image_files = []
        self.index_exact = {}
        self.index_ascii = {}
        self.index_condensed = {}
        self.rescan()

    def rescan(self):
        """Skanuje folder i buduje indeks dopasowań."""
        self.image_files.clear()
        self.index_exact.clear()
        self.index_ascii.clear()
        self.index_condensed.clear()

        if not os.path.isdir(self.folder_path):
            return

        for fname in os.listdir(self.folder_path):
            full_path = os.path.join(self.folder_path, fname)
            if not os.path.isfile(full_path):
                continue

            base, ext = os.path.splitext(fname)
            if ext.lower() not in self.ALLOWED_EXTENSIONS:
                continue

            self.image_files.append(fname)
            n_base = norm_text(base)
            asc_base = strip_diacritics(n_base)
            condensed = re.sub(r"[\s\-_]+", "", n_base)

            if n_base not in self.index_exact or ext.lower() != '.webp':
                self.index_exact[n_base] = full_path
            if asc_base not in self.index_ascii or ext.lower() != '.webp':
                self.index_ascii[asc_base] = full_path
            if condensed not in self.index_condensed or ext.lower() != '.webp':
                self.index_condensed[condensed] = full_path

    def count(self) -> int:
        return len(self.image_files)

    def find_match(self, dish_name: str) -> tuple[str | None, str | None]:
        """
        Zwraca (ścieżka_do_pliku, opis_dopasowania) lub (None, None).
        Jeśli plik to .webp i włączona jest konwersja, zwraca ścieżkę do .png.
        """
        n_dish = norm_text(dish_name)
        if not n_dish:
            return None, None

        # 1. Dokładne dopasowanie po znormalizowanym tekście
        if n_dish in self.index_exact:
            matched_path = self.index_exact[n_dish]
            final_path = self._prepare_image_file(matched_path)
            return final_path, f"dokładne: '{os.path.basename(matched_path)}'"

        # 2. Dopasowanie z usuniętymi znakami diakrytycznymi
        asc_dish = strip_diacritics(n_dish)
        if asc_dish in self.index_ascii:
            matched_path = self.index_ascii[asc_dish]
            final_path = self._prepare_image_file(matched_path)
            return final_path, f"ASCII: '{os.path.basename(matched_path)}'"

        # 3. Dopasowanie bez spacji i myślników
        condensed = re.sub(r"[\s\-_]+", "", n_dish)
        if condensed in self.index_condensed:
            matched_path = self.index_condensed[condensed]
            final_path = self._prepare_image_file(matched_path)
            return final_path, f"elastyczne: '{os.path.basename(matched_path)}'"

        return None, None

    def _prepare_image_file(self, file_path: str) -> str:
        """Konwertuje .webp na .png w katalogu tymczasowym / cache, jeśli to konieczne."""
        _, ext = os.path.splitext(file_path)
        if ext.lower() != '.webp' or not self.auto_convert_webp:
            return file_path

        try:
            os.makedirs(self.cache_dir, exist_ok=True)
            base_name = os.path.splitext(os.path.basename(file_path))[0]
            png_name = f"{base_name}.png"
            target_path = os.path.join(self.cache_dir, png_name)

            if os.path.exists(target_path) and os.path.getmtime(target_path) >= os.path.getmtime(file_path):
                return target_path

            with Image.open(file_path) as im:
                im.convert("RGBA").save(target_path, "PNG")
            return target_path
        except Exception as e:
            self.log_func(f"[Ostrzeżenie] Nie udało się skonwertować .webp ({os.path.basename(file_path)}): {e}")
            return file_path


# ==============================================================================
# UI COMPONENTS (DARK SLATE THEME)
# ==============================================================================

class ModernButton(tk.Button):
    def __init__(self, master, text, command=None, bg="#3b82f6", fg="white",
                 hover_bg="#2563eb", active_bg="#1d4ed8", font=("Segoe UI", 10, "bold"),
                 relief="flat", bd=0, padx=14, pady=8, **kwargs):
        super().__init__(master, text=text, command=command, bg=bg, fg=fg,
                         font=font, relief=relief, bd=bd, padx=padx, pady=pady,
                         activebackground=active_bg, activeforeground=fg, cursor="hand2", **kwargs)
        self.default_bg = bg
        self.hover_bg = hover_bg
        self.active_bg = active_bg
        self.bind("<Enter>", self.on_enter)
        self.bind("<Leave>", self.on_leave)

    def on_enter(self, event):
        if str(self['state']) != 'disabled':
            self.config(bg=self.hover_bg)

    def on_leave(self, event):
        if str(self['state']) != 'disabled':
            self.config(bg=self.default_bg)


class ModernCheckbutton(tk.Frame):
    def __init__(self, master, text, variable, accent="#3b82f6", fg="#f1f5f9", bg="#1e293b",
                 font=("Segoe UI", 10), **kwargs):
        super().__init__(master, bg=bg, cursor="hand2", **kwargs)
        self.var = variable
        self.accent = accent
        self.bg = bg
        self.fg = fg

        self.box = tk.Canvas(self, width=18, height=18, bg=bg, highlightthickness=0)
        self.box.pack(side="left")

        self.label = tk.Label(self, text=text, font=font, fg=fg, bg=bg, cursor="hand2")
        self.label.pack(side="left", padx=(8, 0))

        self.bind("<Button-1>", self.toggle)
        self.box.bind("<Button-1>", self.toggle)
        self.label.bind("<Button-1>", self.toggle)

        self.redraw()
        self.var.trace_add("write", lambda *a: self.redraw())

    def toggle(self, event=None):
        self.var.set(not self.var.get())

    def redraw(self):
        self.box.delete("all")
        if self.var.get():
            self.box.create_rectangle(1, 1, 17, 17, outline=self.accent, fill=self.accent, width=0)
            self.box.create_line(4, 9, 8, 13, width=2, fill="white", capstyle="round")
            self.box.create_line(8, 13, 14, 5, width=2, fill="white", capstyle="round")
        else:
            self.box.create_rectangle(1, 1, 17, 17, outline="#475569", fill=self.bg, width=1)


# ==============================================================================
# MAIN APPLICATION GUI & AUTOMATION LOGIC
# ==============================================================================

class PhotoUploaderGUI:
    def __init__(self, root):
        self.root = root
        self.root.title(f"Papu Photo Uploader {VERSION}")
        self.root.geometry("1040x780")
        self.root.minsize(880, 600)

        self.url = "https://system.papu.io/settings/menu-edit"
        self.driver = None
        self.upload_thread = None
        self.uploading = False
        self._stop_requested = False
        self._log_lines = []

        # Theme Colors
        self.colors = {
            'bg': "#0f172a",
            'panel': "#1e293b",
            'footer': "#020617",
            'accent': "#3b82f6",
            'accent_hover': "#2563eb",
            'success': "#10b981",
            'success_hover': "#059669",
            'danger': "#ef4444",
            'danger_hover': "#dc2626",
            'warning': "#f59e0b",
            'text_main': "#f8fafc",
            'text_muted': "#94a3b8",
            'border': "#334155"
        }

        # Settings
        self.folder_var = tk.StringVar(value=os.path.abspath("zdjecia_menu"))
        self.scope_var = tk.StringVar(value="all")  # "all" lub "current"
        self.skip_existing_var = tk.BooleanVar(value=True)
        self.convert_webp_var = tk.BooleanVar(value=True)
        self.wait_time_var = tk.DoubleVar(value=2.5)

        self.matcher = ImageMatcher(
            self.folder_var.get(),
            auto_convert_webp=self.convert_webp_var.get(),
            log_func=self.log_print
        )

        self.setup_ui()
        self.update_photos_count()

    # --------------------------------------------------------------------------
    # UI SETUP
    # --------------------------------------------------------------------------
    def setup_ui(self):
        self.root.configure(bg=self.colors['bg'])

        # Style configuration
        style = ttk.Style()
        style.theme_use('default')
        style.configure("Custom.Horizontal.TProgressbar",
                        background=self.colors['accent'],
                        troughcolor=self.colors['panel'],
                        bordercolor=self.colors['border'],
                        lightcolor=self.colors['accent'],
                        darkcolor=self.colors['accent'])

        # Header
        header = tk.Frame(self.root, bg=self.colors['panel'], padx=20, pady=14, bd=0)
        header.pack(fill="x")

        title_box = tk.Frame(header, bg=self.colors['panel'])
        title_box.pack(side="left")

        tk.Label(title_box, text="📸 Papu Photo Uploader", font=("Segoe UI", 17, "bold"),
                 bg=self.colors['panel'], fg=self.colors['text_main']).pack(anchor="w")
        tk.Label(title_box, text="Automatyczne wgrywanie zdjęć dań na podstawie nazw",
                 font=("Segoe UI", 9), bg=self.colors['panel'], fg=self.colors['text_muted']).pack(anchor="w")

        # Top Buttons
        top_btns = tk.Frame(header, bg=self.colors['panel'])
        top_btns.pack(side="right")

        ModernButton(top_btns, text="⚙️ Dane logowania", command=self.open_settings_window,
                     bg="#334155", hover_bg="#475569", padx=10, pady=6, font=("Segoe UI", 9)).pack(side="left", padx=5)
        ModernButton(top_btns, text="🔍 Podgląd zdjęć", command=self.preview_images_window,
                     bg="#334155", hover_bg="#475569", padx=10, pady=6, font=("Segoe UI", 9)).pack(side="left", padx=5)

        # Main Layout
        content = tk.Frame(self.root, bg=self.colors['bg'], padx=20, pady=15)
        content.pack(fill="both", expand=True)

        # Controls Panel
        controls_card = tk.Frame(content, bg=self.colors['panel'], padx=18, pady=16,
                                 highlightbackground=self.colors['border'], highlightthickness=1)
        controls_card.pack(fill="x", pady=(0, 12))

        # Folder row
        f_row = tk.Frame(controls_card, bg=self.colors['panel'])
        f_row.pack(fill="x", pady=(0, 10))

        tk.Label(f_row, text="📁 Katalog ze zdjęciami:", font=("Segoe UI", 10, "bold"),
                 bg=self.colors['panel'], fg=self.colors['text_main']).pack(side="left")

        self.count_label = tk.Label(f_row, text="", font=("Segoe UI", 9),
                                    bg=self.colors['panel'], fg=self.colors['warning'])
        self.count_label.pack(side="right")

        f_input_row = tk.Frame(controls_card, bg=self.colors['panel'])
        f_input_row.pack(fill="x", pady=(0, 14))

        self.folder_entry = tk.Entry(f_input_row, textvariable=self.folder_var, font=("Segoe UI", 10),
                                     bg="#0f172a", fg=self.colors['text_main'], relief="flat", bd=1,
                                     highlightbackground=self.colors['border'], highlightthickness=1)
        self.folder_entry.pack(side="left", fill="x", expand=True, ipady=4, padx=(0, 10))

        ModernButton(f_input_row, text="Przeglądaj...", command=self.choose_folder,
                     bg="#334155", hover_bg="#475569", padx=12, pady=4, font=("Segoe UI", 9)).pack(side="left")

        # Options Row
        opts_row = tk.Frame(controls_card, bg=self.colors['panel'])
        opts_row.pack(fill="x")

        # Scope radio buttons
        scope_frame = tk.Frame(opts_row, bg=self.colors['panel'])
        scope_frame.pack(side="left", padx=(0, 20))

        tk.Label(scope_frame, text="Zakres pracy:", font=("Segoe UI", 9, "bold"),
                 bg=self.colors['panel'], fg=self.colors['text_muted']).pack(anchor="w")

        r_box = tk.Frame(scope_frame, bg=self.colors['panel'])
        r_box.pack(anchor="w", pady=(2, 0))

        r1 = tk.Radiobutton(r_box, text="Wszystkie kategorie", variable=self.scope_var, value="all",
                            bg=self.colors['panel'], fg=self.colors['text_main'], selectcolor=self.colors['bg'],
                            activebackground=self.colors['panel'], activeforeground=self.colors['text_main'],
                            font=("Segoe UI", 9))
        r1.pack(side="left", padx=(0, 10))

        r2 = tk.Radiobutton(r_box, text="Tylko bieżąca kategoria", variable=self.scope_var, value="current",
                            bg=self.colors['panel'], fg=self.colors['text_main'], selectcolor=self.colors['bg'],
                            activebackground=self.colors['panel'], activeforeground=self.colors['text_main'],
                            font=("Segoe UI", 9))
        r2.pack(side="left")

        # Checkboxes
        chk_frame = tk.Frame(opts_row, bg=self.colors['panel'])
        chk_frame.pack(side="left", padx=(0, 20))

        ModernCheckbutton(chk_frame, text="Pomiń dania z już wgranym zdjęciem",
                          variable=self.skip_existing_var).pack(anchor="w", pady=2)
        ModernCheckbutton(chk_frame, text="Automatycznie konwertuj .webp do .png",
                          variable=self.convert_webp_var).pack(anchor="w", pady=2)

        # Wait time
        wait_frame = tk.Frame(opts_row, bg=self.colors['panel'])
        wait_frame.pack(side="right")

        tk.Label(wait_frame, text="Oczekiwanie na zapis (s):", font=("Segoe UI", 9, "bold"),
                 bg=self.colors['panel'], fg=self.colors['text_muted']).pack(anchor="w")
        wait_spin = tk.Spinbox(wait_frame, from_=1.0, to=10.0, increment=0.5,
                               textvariable=self.wait_time_var, width=6, font=("Segoe UI", 9),
                               bg="#0f172a", fg="white", relief="flat", bd=1,
                               highlightbackground=self.colors['border'], highlightthickness=1)
        wait_spin.pack(anchor="w", pady=(2, 0), ipady=2)

        # Action Buttons Row
        actions_card = tk.Frame(content, bg=self.colors['panel'], padx=16, pady=12,
                                highlightbackground=self.colors['border'], highlightthickness=1)
        actions_card.pack(fill="x", pady=(0, 12))

        self.btn_open_chrome = ModernButton(actions_card, text="🌐 1. Otwórz Chrome", command=self.start_chrome_thread,
                                            bg=self.colors['accent'], hover_bg=self.colors['accent_hover'], padx=16)
        self.btn_open_chrome.pack(side="left", padx=(0, 10))

        self.btn_start = ModernButton(actions_card, text="🚀 2. ROZPOCZNIJ WGRYWANIE ZDJĘĆ", command=self.start_upload,
                                      bg=self.colors['success'], hover_bg=self.colors['success_hover'], padx=20)
        self.btn_start.pack(side="left", padx=(0, 10))

        self.btn_stop = ModernButton(actions_card, text="⏹ ZATRZYMAJ", command=self.stop_upload,
                                     bg=self.colors['danger'], hover_bg=self.colors['danger_hover'], padx=20)

        self.status_label = tk.Label(actions_card, text="Gotowy do uruchomienia Chrome", font=("Segoe UI", 9),
                                     bg=self.colors['panel'], fg=self.colors['text_muted'])
        self.status_label.pack(side="right", padx=10)

        # Progress Bar Card
        progress_card = tk.Frame(content, bg=self.colors['panel'], padx=16, pady=8,
                                 highlightbackground=self.colors['border'], highlightthickness=1)
        progress_card.pack(fill="x", pady=(0, 12))

        p_info = tk.Frame(progress_card, bg=self.colors['panel'])
        p_info.pack(fill="x", pady=(0, 4))

        self.progress_title = tk.Label(p_info, text="Postęp wgrywania:", font=("Segoe UI", 9, "bold"),
                                       bg=self.colors['panel'], fg=self.colors['text_main'])
        self.progress_title.pack(side="left")

        self.progress_percent = tk.Label(p_info, text="0%", font=("Segoe UI", 9),
                                         bg=self.colors['panel'], fg=self.colors['text_muted'])
        self.progress_percent.pack(side="right")

        self.progress_bar = ttk.Progressbar(progress_card, style="Custom.Horizontal.TProgressbar",
                                            mode="determinate")
        self.progress_bar.pack(fill="x", ipady=2)

        # Logs Console
        logs_card = tk.Frame(content, bg=self.colors['panel'], padx=12, pady=10,
                             highlightbackground=self.colors['border'], highlightthickness=1)
        logs_card.pack(fill="both", expand=True)

        l_head = tk.Frame(logs_card, bg=self.colors['panel'])
        l_head.pack(fill="x", pady=(0, 6))

        tk.Label(l_head, text="📜 Konsola zdarzeń i logi na żywo:", font=("Segoe UI", 9, "bold"),
                 bg=self.colors['panel'], fg=self.colors['text_main']).pack(side="left")

        ModernButton(l_head, text="Wyczyść logi", command=self.clear_logs,
                     bg="#334155", hover_bg="#475569", padx=8, pady=2, font=("Segoe UI", 8)).pack(side="right", padx=4)
        ModernButton(l_head, text="Zapisz do pliku", command=self.save_logs_to_file,
                     bg="#334155", hover_bg="#475569", padx=8, pady=2, font=("Segoe UI", 8)).pack(side="right", padx=4)

        log_frame = tk.Frame(logs_card, bg="#0f172a")
        log_frame.pack(fill="both", expand=True)

        self.log_text = tk.Text(log_frame, bg="#0b0f19", fg="#f8fafc", font=("Consolas", 9),
                                bd=0, padx=8, pady=8, wrap="word", relief="flat")
        log_scroll = tk.Scrollbar(log_frame, command=self.log_text.yview)
        self.log_text.config(yscrollcommand=log_scroll.set)

        log_scroll.pack(side="right", fill="y")
        self.log_text.pack(side="left", fill="both", expand=True)

        # Log color tags
        self.log_text.tag_config("info", foreground="#94a3b8")
        self.log_text.tag_config("success", foreground="#10b981")
        self.log_text.tag_config("warning", foreground="#f59e0b")
        self.log_text.tag_config("error", foreground="#ef4444")
        self.log_text.tag_config("upload", foreground="#38bdf8", font=("Consolas", 9, "bold"))
        self.log_text.tag_config("skip", foreground="#a78bfa")

        # Initial message
        self.log_print(f"Program gotowy. Wersja {VERSION}", "info")
        self.log_print(f"Domyślny URL: {self.url}", "info")

    # --------------------------------------------------------------------------
    # HELPERS & LOGGING
    # --------------------------------------------------------------------------
    def log_print(self, text: str, tag: str = "info"):
        timestamp = datetime.now().strftime("%H:%M:%S")
        formatted = f"[{timestamp}] {text}\n"
        self._log_lines.append(formatted)

        def append():
            self.log_text.insert("end", formatted, tag)
            self.log_text.see("end")

        self.root.after(0, append)

    def clear_logs(self):
        self.log_text.delete("1.0", "end")
        self._log_lines.clear()

    def save_logs_to_file(self):
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        fname = f"photo_upload_log_{ts}.txt"
        try:
            with open(fname, "w", encoding="utf-8") as f:
                f.writelines(self._log_lines)
            messagebox.showinfo("Zapisano", f"Logi zostały zapisane do pliku: {fname}")
        except Exception as e:
            messagebox.showerror("Błąd", f"Nie udało się zapisać pliku: {e}")

    def update_photos_count(self):
        count = self.matcher.count()
        if count > 0:
            self.count_label.config(text=f"Znaleziono {count} zdjęć w folderze", fg=self.colors['success'])
        else:
            self.count_label.config(text="Brak plików zdjęć w folderze!", fg=self.colors['danger'])

    def choose_folder(self):
        selected = filedialog.askdirectory(initialdir=self.folder_var.get(), title="Wybierz folder ze zdjęciami")
        if selected:
            self.folder_var.set(selected)
            self.matcher = ImageMatcher(selected, auto_convert_webp=self.convert_webp_var.get(), log_func=self.log_print)
            self.update_photos_count()
            self.log_print(f"Zmieniono folder zdjęć na: {selected} ({self.matcher.count()} plików)", "info")

    def preview_images_window(self):
        top = tk.Toplevel(self.root)
        top.title("Podgląd plików w folderze")
        top.geometry("600x450")
        top.configure(bg=self.colors['panel'])

        tk.Label(top, text=f"Lista zdjęć w folderze ({self.matcher.count()} plików):",
                 font=("Segoe UI", 11, "bold"), bg=self.colors['panel'], fg="white").pack(pady=10, padx=15, anchor="w")

        list_frame = tk.Frame(top, bg="#0f172a")
        list_frame.pack(fill="both", expand=True, padx=15, pady=(0, 15))

        txt = tk.Text(list_frame, bg="#0b0f19", fg="#f8fafc", font=("Consolas", 9), bd=0, padx=8, pady=8)
        scr = tk.Scrollbar(list_frame, command=txt.yview)
        txt.config(yscrollcommand=scr.set)
        scr.pack(side="right", fill="y")
        txt.pack(side="left", fill="both", expand=True)

        for img in sorted(self.matcher.image_files):
            txt.insert("end", f"• {img}\n")
        txt.config(state="disabled")

    # --------------------------------------------------------------------------
    # SETTINGS & AUTO LOGIN
    # --------------------------------------------------------------------------
    def load_settings(self):
        if os.path.exists("settings.json"):
            try:
                with open("settings.json", "r", encoding="utf-8") as f:
                    data = json.load(f)
                    return data.get("email", ""), data.get("password", "")
            except Exception:
                pass
        return "", ""

    def open_settings_window(self):
        top = tk.Toplevel(self.root)
        top.title("Ustawienia Logowania")
        top.geometry("400x320")
        top.configure(bg=self.colors['panel'])
        top.resizable(False, False)

        tk.Label(top, text="🔐 Dane do Auto-Logowania", font=("Segoe UI", 12, "bold"),
                 bg=self.colors['panel'], fg="white").pack(pady=(20, 5))
        tk.Label(top, text="Zapisz email i hasło do systemu Papu.io", font=("Segoe UI", 9),
                 bg=self.colors['panel'], fg=self.colors['text_muted']).pack(pady=(0, 20))

        form = tk.Frame(top, bg=self.colors['panel'], padx=30)
        form.pack(fill="x")

        saved_email, saved_pass = self.load_settings()

        tk.Label(form, text="Email:", bg=self.colors['panel'], fg="#cbd5e1", font=("Segoe UI", 9)).pack(anchor="w")
        email_entry = tk.Entry(form, font=("Segoe UI", 10), bg="#0f172a", fg="white", relief="flat", bd=1,
                               highlightthickness=1, highlightbackground=self.colors['border'])
        email_entry.pack(fill="x", pady=(2, 10), ipady=4)
        email_entry.insert(0, saved_email)

        tk.Label(form, text="Hasło:", bg=self.colors['panel'], fg="#cbd5e1", font=("Segoe UI", 9)).pack(anchor="w")
        pass_entry = tk.Entry(form, font=("Segoe UI", 10), bg="#0f172a", fg="white", relief="flat", bd=1,
                              highlightthickness=1, highlightbackground=self.colors['border'], show="•")
        pass_entry.pack(fill="x", pady=(2, 20), ipady=4)
        pass_entry.insert(0, saved_pass)

        def save():
            try:
                with open("settings.json", "w", encoding="utf-8") as f:
                    json.dump({"email": email_entry.get().strip(), "password": pass_entry.get().strip()}, f, indent=4)
                messagebox.showinfo("Sukces", "Zapisano dane logowania!")
                top.destroy()
            except Exception as e:
                messagebox.showerror("Błąd", f"Nie udało się zapisać: {e}")

        ModernButton(form, text="Zapisz", command=save, bg=self.colors['accent'],
                     hover_bg=self.colors['accent_hover']).pack(fill="x", pady=10)

    def _perform_auto_login(self, driver):
        email, password = self.load_settings()
        if not email or not password:
            self.log_print("Brak zapisanych danych w settings.json - zaloguj się ręcznie w Chrome.", "warning")
            return

        self.log_print("Wykonywanie automatycznego logowania...", "info")
        wait = WebDriverWait(driver, 10)
        try:
            email_field = wait.until(EC.visibility_of_element_located((By.ID, "email-address")))
            email_field.clear()
            email_field.send_keys(email)

            pass_field = driver.find_element(By.ID, "password")
            pass_field.clear()
            pass_field.send_keys(password)

            login_btn = wait.until(EC.element_to_be_clickable((By.XPATH, "//button[contains(., 'Zaloguj się')]")))
            time.sleep(0.5)
            login_btn.click()
            self.log_print("Formularz logowania zatwierdzony.", "success")
        except Exception as e:
            self.log_print(f"Auto-login: pominięto lub strona już zalogowana ({e})", "info")

    # --------------------------------------------------------------------------
    # CHROME LIFECYCLE
    # --------------------------------------------------------------------------
    def start_chrome_thread(self):
        def run():
            try:
                self.log_print("Uruchamianie przeglądarki Chrome...", "info")
                self.status_label.config(text="Uruchamianie Chrome...")
                options = webdriver.ChromeOptions()
                options.add_argument("--start-maximized")
                self.driver = webdriver.Chrome(service=Service(ChromeDriverManager().install()), options=options)

                self.log_print(f"Otwieram stronę: {self.url}", "info")
                self.driver.get(self.url)
                self._perform_auto_login(self.driver)

                self.log_print("Chrome jest gotowy. Upewnij się, że jesteś w menu i kliknij '2. ROZPOCZNIJ WGRYWANIE ZDJĘĆ'", "success")
                self.status_label.config(text="Chrome uruchomiony (Gotowy do wgrywania)")
            except Exception as e:
                self.log_print(f"Błąd Chrome: {e}", "error")
                self.status_label.config(text="Błąd uruchamiania Chrome")

        threading.Thread(target=run, daemon=True).start()

    # --------------------------------------------------------------------------
    # AUTOMATION WORKFLOW
    # --------------------------------------------------------------------------
    def start_upload(self):
        if not self.driver:
            messagebox.showwarning("Uwaga", "Najpierw uruchom Chrome (krok 1)!")
            return

        if self.matcher.count() == 0:
            messagebox.showwarning("Uwaga", "Brak zdjęć w wybranym folderze!")
            return

        if self.uploading:
            return

        self.uploading = True
        self._stop_requested = False
        self.btn_start.pack_forget()
        self.btn_stop.pack(side="left", padx=(0, 10))
        self.status_label.config(text="Trwa proces wgrywania zdjęć...")

        self.upload_thread = threading.Thread(target=self._run_upload_loop, daemon=True)
        self.upload_thread.start()

    def stop_upload(self):
        if not self.uploading:
            return
        self.log_print("=== ZATRZYMYWANIE NA ŻĄDANIE UŻYTKOWNIKA ===", "warning")
        self._stop_requested = True
        self.status_label.config(text="Zatrzymywanie...")

    def _finish_upload(self, message="Zakończono proces wgrywania."):
        self.uploading = False
        self._stop_requested = False

        def restore():
            self.btn_stop.pack_forget()
            self.btn_start.pack(side="left", padx=(0, 10))
            self.status_label.config(text=message)

        self.root.after(0, restore)

    def _safe_click(self, driver, el):
        """Bezpieczne klikanie z automatycznym przewinięciem i fallbackiem do JS."""
        try:
            driver.execute_script("arguments[0].scrollIntoView({block:'center'});", el)
            time.sleep(0.2)
            el.click()
        except Exception:
            driver.execute_script("arguments[0].click();", el)

    def _close_modals(self, driver):
        """Zamyka ewentualne modale (np. menuSourceModal) blokujące klikanie."""
        try:
            modals = driver.find_elements(By.CSS_SELECTOR, "div.modal.show, div#menuSourceModal")
            for m in modals:
                if m.is_displayed():
                    close_btns = m.find_elements(By.CSS_SELECTOR, "button.close, [aria-label='Close'], button.btn-secondary, .modal-footer button")
                    if close_btns:
                        driver.execute_script("arguments[0].click();", close_btns[0])
                        time.sleep(0.5)
                    else:
                        driver.execute_script("arguments[0].style.display = 'none'; arguments[0].classList.remove('show');", m)
            driver.execute_script("document.querySelectorAll('.modal-backdrop').forEach(b => b.remove());")
        except Exception:
            pass

    def _goto_dishes_tab(self, wait):
        """Przechodzi do zakładki Dania, jeśli nie jest aktywna."""
        try:
            tab_xpath = "//button[contains(@class,'filter__btn') and .//span[contains(normalize-space(text()), 'Dania')]]"
            btn = wait.until(EC.presence_of_element_located((By.XPATH, tab_xpath)))
            classes = btn.get_attribute("class") or ""
            if "active" not in classes:
                self._safe_click(self.driver, btn)
                time.sleep(1)
        except Exception as e:
            self.log_print(f"Nawigacja do zakładki 'Dania': {e}", "info")

    def _return_to_categories_list(self, driver, wait):
        """Wraca do listy kategorii (klikając Wróć lub zakładkę Dania)."""
        # 1. Kliknij właściwy przycisk Wróć (tylko w nagłówku kategorii dań, NIGDY wyjście z menu)
        try:
            # Wyszukaj przycisk powrotu wewnątrz kategorii:
            # - Posiada klasę btn-light oraz mr-2
            # - Zawiera ikonę fa-arrow-left BEZ klasy icon--close
            # - NIE posiada atrybutu 'Powrót do poprzedniej strony' (który zamyka całe menu)
            xpath_back = (
                "//button[contains(@class,'btn-light') and contains(@class,'mr-2') and "
                ".//i[contains(@class,'fa-arrow-left') and not(contains(@class,'icon--close')) and not(contains(@aria-label,'poprzedniej'))]]"
            )
            back_btns = driver.find_elements(By.XPATH, xpath_back)

            # Fallback: Dokładny selektor CSS sprawdzony w writer (1).py
            if not back_btns:
                candidates = driver.find_elements(By.CSS_SELECTOR, "button.btn.mr-2.btn-light.btn-sm")
                back_btns = [
                    b for b in candidates
                    if "icon--close" not in (b.get_attribute("innerHTML") or "")
                    and "poprzedniej" not in (b.get_attribute("innerHTML") or "")
                    and "Bolt" not in (b.text or "")
                ]

            for b in back_btns:
                if b.is_displayed():
                    self.log_print("Klikam przycisk 'Wróć' (powrót do listy kategorii)...", "info")
                    self._safe_click(driver, b)
                    time.sleep(1.2)
                    break
        except Exception as e:
            self.log_print(f"Ostrzeżenie przy klikaniu Wróć: {e}", "info")

        # 2. Zamknij ewentualny modal, jeśli się pojawił
        self._close_modals(driver)

        # 3. Jeśli lista kategorii nadal nie jest widoczna, kliknij zakładkę 'Dania'
        try:
            cat_list = driver.find_elements(By.XPATH, "//div[contains(@class,'list-group-item') and .//span]")
            if not cat_list or not cat_list[0].is_displayed():
                tab_xpath = "//button[contains(@class,'filter__btn') and .//span[contains(normalize-space(text()), 'Dania')]]"
                tab_btns = driver.find_elements(By.XPATH, tab_xpath)
                if tab_btns:
                    self.log_print("Przełączam na zakładkę 'Dania' w celu powrotu do kategorii...", "info")
                    self._safe_click(driver, tab_btns[0])
                    time.sleep(1.2)
        except Exception:
            pass

    def _run_upload_loop(self):
        try:
            driver = self.driver
            wait = WebDriverWait(driver, 10)
            wait_delay = max(1.0, float(self.wait_time_var.get()))
            skip_existing = self.skip_existing_var.get()
            scope = self.scope_var.get()

            # Odśwież indeks zdjęć
            self.matcher.auto_convert_webp = self.convert_webp_var.get()
            self.matcher.rescan()

            self.log_print("=== ROZPOCZYNAM WGRYWANIE ZDJĘĆ ===", "success")
            self.log_print(f"Zakres: {'Wszystkie kategorie' if scope == 'all' else 'Tylko bieżąca kategoria'}", "info")
            self.log_print(f"Pomiń dania z już wgranym zdjęciem: {'TAK' if skip_existing else 'NIE'}", "info")
            self.log_print(f"Czas oczekiwania na auto-zapis: {wait_delay:.1f}s", "info")

            self._close_modals(driver)
            self._goto_dishes_tab(wait)

            if scope == "current":
                self._process_current_category(driver, wait, wait_delay, skip_existing)
            else:
                self._process_all_categories(driver, wait, wait_delay, skip_existing)

            if self._stop_requested:
                self.log_print("Proces przerwany przez użytkownika.", "warning")
                self._finish_upload("Zatrzymano przez użytkownika.")
            else:
                self.log_print("🎉 WSZYSTKIE KATEGORIE I DANIA ZOSTAŁY PRZETWORZONE!", "success")
                self._finish_upload("Wgrywanie zakończone pomyślnie!")

        except Exception as e:
            self.log_print(f"Krytyczny błąd podczas pracy: {e}", "error")
            self._finish_upload("Błąd podczas wgrywania.")

    def _process_all_categories(self, driver, wait, wait_delay, skip_existing):
        """Przechodzi po kolei po wszystkich kategoriach w menu."""
        # Wróć do listy kategorii, jeśli byliśmy wewnątrz jakiejś
        self._return_to_categories_list(driver, wait)

        # Pobierz nazwy wszystkich kategorii
        time.sleep(0.8)
        self._close_modals(driver)
        wait.until(EC.presence_of_element_located((By.XPATH, "//div[contains(@class,'list-group-item') and .//span]")))
        time.sleep(0.5)
        cat_elements = driver.find_elements(By.XPATH, "//div[contains(@class,'list-group-item') and .//span]")

        categories = []
        for el in cat_elements:
            try:
                sp = el.find_element(By.XPATH, ".//span[normalize-space(.)]")
                t = sp.text.strip()
                if t and t not in categories:
                    categories.append(t)
            except Exception:
                continue

        self.log_print(f"Wykryto {len(categories)} kategorii: {', '.join(categories)}", "info")

        total_cats = len(categories)
        for c_idx, cat_name in enumerate(categories, start=1):
            if self._stop_requested:
                break

            self.log_print(f"\n📂 [{c_idx}/{total_cats}] Otwieram kategorię: '{cat_name}'", "upload")

            self._close_modals(driver)

            # Kliknij kategorię po nazwie z użyciem safe_click
            cat_xpath = f"//div[contains(@class,'list-group-item') and .//span[normalize-space(text())='{cat_name}']]"
            try:
                cat_el = wait.until(EC.presence_of_element_located((By.XPATH, cat_xpath)))
                self._safe_click(driver, cat_el)
                time.sleep(1.2)
            except Exception as e:
                self.log_print(f"Nie udało się otworzyć kategorii '{cat_name}': {e}", "error")
                continue

            # Przetwórz dania w tej kategorii
            self._process_current_category(driver, wait, wait_delay, skip_existing, cat_name=cat_name)

            # Wróć do listy kategorii przed kolejną iteracją
            self._return_to_categories_list(driver, wait)

    def _process_current_category(self, driver, wait, wait_delay, skip_existing, cat_name="Bieżąca"):
        """Przetwarza wszystkie dania w aktualnie otwartej kategorii."""
        time.sleep(1)
        dish_rows = driver.find_elements(By.XPATH, "//div[contains(@class,'list-group-item--draggable')]")
        if not dish_rows:
            self.log_print(f"Brak dań w kategorii '{cat_name}' (lub lista się nie załadowała).", "info")
            return

        dish_names = []
        for row in dish_rows:
            try:
                sp = row.find_element(By.XPATH, ".//span[normalize-space(.)]")
                d_name = sp.text.strip()
                if d_name:
                    dish_names.append(d_name)
            except Exception:
                continue

        total_dishes = len(dish_names)
        self.log_print(f"Kategoria '{cat_name}' zawiera {total_dishes} dań.", "info")

        for d_idx, dish_name in enumerate(dish_names, start=1):
            if self._stop_requested:
                break

            pct = int((d_idx / total_dishes) * 100)
            self.progress_percent.config(text=f"{pct}%")
            self.progress_bar['value'] = pct

            self.log_print(f" [{d_idx}/{total_dishes}] Danie: '{dish_name}'", "info")

            # 1. Znajdź i kliknij danie na liście po lewej
            dish_xpath = f"//div[contains(@class,'list-group-item--draggable') and .//span[normalize-space(text())='{dish_name}']]"
            try:
                d_el = wait.until(EC.presence_of_element_located((By.XPATH, dish_xpath)))
                self._safe_click(driver, d_el)
                # Poczekaj chwilę na załadowanie formularza po prawej stronie
                time.sleep(0.8)
                wait.until(EC.presence_of_element_located((
                    By.CSS_SELECTOR, "div.upload-image-file, input[name='mealName'], input[name='productName']"
                )))
            except Exception as e:
                self.log_print(f"Nie można kliknąć dania '{dish_name}': {e}", "error")
                continue

            # 2. Sprawdź, czy danie ma już wgrane zdjęcie
            if skip_existing:
                has_photo = self._dish_has_photo(driver)
                if has_photo:
                    self.log_print(f"   ⏩ Danie '{dish_name}' posiada już zdjęcie -> POMIJAM", "skip")
                    continue

            # 3. Znajdź pasujące zdjęcie w folderze
            img_path, match_desc = self.matcher.find_match(dish_name)
            if not img_path:
                self.log_print(f"   ⚠️ Brak pasującego zdjęcia w folderze dla: '{dish_name}'", "warning")
                continue

            self.log_print(f"   🎯 Dopasowano plik: {os.path.basename(img_path)} ({match_desc})", "info")

            # 4. Wgraj plik przez input[type="file"]
            try:
                file_input = wait.until(EC.presence_of_element_located((
                    By.CSS_SELECTOR, "div.upload-image-file input[type='file'], input.custom-file-input[type='file']"
                )))

                driver.execute_script(
                    "arguments[0].style.display = 'block'; "
                    "arguments[0].style.visibility = 'visible'; "
                    "arguments[0].style.opacity = '1'; "
                    "arguments[0].style.zIndex = '9999'; "
                    "arguments[0].removeAttribute('hidden');",
                    file_input
                )

                abs_path = os.path.abspath(img_path)
                file_input.send_keys(abs_path)

                driver.execute_script(
                    "arguments[0].dispatchEvent(new Event('change', { bubbles: true }));",
                    file_input
                )

                self.log_print(f"   📸 Wysłano plik -> Czekam {wait_delay:.1f}s na auto-zapis...", "upload")
                time.sleep(wait_delay)
                self.log_print(f"   ✅ Zapisano pomyślnie dla: '{dish_name}'", "success")

            except Exception as e:
                self.log_print(f"   ❌ Błąd podczas wysyłania zdjęcia dla '{dish_name}': {e}", "error")

    def _dish_has_photo(self, driver) -> bool:
        """
        Precyzyjnie sprawdza w formularzu dania, czy zdjęcie jest już załadowane.
        Zwraca False, jeśli etykieta to 'Załaduj plik' lub kosz jest wyłączony (disabled).
        """
        try:
            js_check = """
                const uploadOuter = document.querySelector('div.upload-image-file');
                if (!uploadOuter) return false;

                // 1. Sprawdź etykietę wewnątrz upload-image-file
                const labelSpan = uploadOuter.querySelector('.custom-file-label span, .form-file-text');
                const labelText = labelSpan ? labelSpan.textContent.trim() : '';

                // Gdy brak zdjęcia, etykieta zawsze zawiera tekst "Załaduj plik"
                if (labelText === 'Załaduj plik') {
                    return false;
                }

                // 2. Sprawdź przycisk kosza znajdujący się OBOK (w tym samym kontenerze .d-flex)
                const container = uploadOuter.closest('div.d-flex') || uploadOuter.parentElement;
                const trashBtn = container ? container.querySelector('button.btn-danger, button.btn-input') : null;

                if (trashBtn) {
                    const isTrashDisabled = trashBtn.disabled || trashBtn.hasAttribute('disabled') || trashBtn.classList.contains('disabled');
                    if (isTrashDisabled) {
                        return false;
                    }
                    if (labelText && labelText !== 'Załaduj plik') {
                        return true;
                    }
                }

                // 3. Sprawdź czy jest miniatura (img) w sekcji zdjęcia
                const imgPreview = container ? container.querySelector('img') : null;
                if (imgPreview && imgPreview.src && !imgPreview.src.includes('data:,')) {
                    return true;
                }

                return false;
            """
            has_photo = driver.execute_script(js_check)
            return bool(has_photo)
        except Exception as e:
            self.log_print(f"Ostrzeżenie przy sprawdzaniu zdjęcia: {e}", "info")
            return False


# ==============================================================================
# ENTRY POINT
# ==============================================================================
if __name__ == "__main__":
    root = tk.Tk()
    app = PhotoUploaderGUI(root)
    root.mainloop()
