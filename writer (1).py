VERSION = "2.0 by Zimny. "
import time
import json
import threading
import tkinter as tk
from tkinter import filedialog, messagebox
import os
import sys
from selenium import webdriver
from selenium.webdriver.chrome.service import Service
from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from webdriver_manager.chrome import ChromeDriverManager
from datetime import datetime
from selenium.webdriver.common.action_chains import ActionChains
import unicodedata
import hashlib
import re
from collections import OrderedDict, defaultdict, Counter
from tkinter import ttk

NBSP = "\xa0"
DASH_CHARS = "\u2010\u2011\u2012\u2013\u2014\u2212"
ZWSP_CHARS = "\u200b\u200c\u200d\u2060"
ELLIPSIS = "\u2026"
PRICE_RE = re.compile(r"([0-9]+(?:[.,][0-9]{1,2})?)")

_PHASE = "dishes"
_ADDONS_RAN = False
_MODIFIERS_RAN = False

# Totale dla każdej fazy
_PHASE_TOTALS = {
    "categories": 0,
    "dishes": 0,
    "sizes": 0,
    "addons": 0,
    "modifiers": 0,
    "ingredients": 0
}


def _set_phase(v, log_func=print):
    global _PHASE, _PHASE_START_TIME, _PHASE_HISTORY


    if v == "ingredients":
        return

    if _PHASE != v:
        # Zapisz wynik poprzedniej fazy
        duration = time.time() - _PHASE_START_TIME
        _PHASE_HISTORY[_PHASE] = duration

        _PHASE = v
        _PHASE_START_TIME = time.time()

        try:
            log_func(f"[FLOW] Phase change: {_PHASE} (Prev took {duration:.1f}s)")
        except Exception:
            pass


def _norm_text(s: str) -> str:
    if not s:
        return ""
    t = unicodedata.normalize("NFKC", str(s))
    t = t.replace(NBSP, " ")
    t = re.sub(f"[{DASH_CHARS}]", "-", t)
    t = re.sub(f"[{ZWSP_CHARS}]", "", t)
    t = t.replace(ELLIPSIS, "...")
    t = re.sub(r"\s+", " ", t).strip()
    return t


def _price_to_float(price_text: str):
    if price_text is None:
        return None
    m = PRICE_RE.search(_norm_text(price_text))
    if not m:
        return None
    val = m.group(1).replace(",", ".")
    try:
        return float(val)
    except:
        return None


def _unique_group_title(item: dict, kind: str) -> str:
    """
    Zwraca unikalny tytuł: '{group_name} — {size_label} ·ABC123'
    POPRAWKA:
    1. Ignoruje kategorię (targets).
    2. Sortuje składniki (alfabetycznie).
    3. USUWA KROPKI z nazw i rozmiarów (żeby "ok." == "ok").
    """
    import hashlib, json as _json

    # Normalizacja + usunięcie kropek (agresywne ujednolicanie)
    base_g = _norm_text(item.get('group_name', '')).replace(".", "")
    base_s = _canon_size_label(item.get('size_label', '')).replace(".", "")
    required = bool(item.get('required', False))

    # 1. Pobieramy listę opcji i normalizujemy ceny
    raw_choices = []
    for c in (item.get('choices') or []):
        nm = _norm_text(c.get('name', ''))
        pr = c.get('price', None)
        if pr is None:
            pr = _price_to_float(c.get('price_text') or "")
        final_price = float(pr) if pr is not None else 0.0
        raw_choices.append((nm, final_price))

    # 2. Sortujemy listę opcji po nazwie
    choices = sorted(raw_choices, key=lambda x: x[0])

    # 3. Payload do hasha
    payload = {
        "k": kind,
        "g": base_g,  # Tu już nie ma kropek
        "s": base_s,  # Tu też nie ma kropek
        "r": required,
        "ch": choices
    }

    # Generujemy hash
    raw = _json.dumps(payload, ensure_ascii=False, separators=(",", ":"))
    short = hashlib.sha1(raw.encode("utf-8")).hexdigest()[:6].upper()

    return f"{base_g} — {base_s} ·{short}"


def _group_exists_in_left_list(wait, title: str) -> bool:
    # szybki check bez czekania całego WebDriverWait
    try:
        d = wait._driver
    except Exception:
        return False
    # Szukaj elementu z UNIKALNYM TYTUŁEM, który jest wewnątrz list-group-item
    els = d.find_elements(By.XPATH,
                          f"//div[contains(@class,'list-group-item')][.//div[contains(@class,'font-weight-medium') and contains(normalize-space(text()), '{title}')]]")
    return len(els) > 0


# ---- HELPERY DO ZAKŁADEK/PRZYCISKÓW ----
def _goto_tab(wait: WebDriverWait, tab_name: str, tab_selector: tuple):
    """
    Klik w zakładkę po napisie na <span> (np. 'Dania', 'Rozmiary').
    tab_selector: (By.XPATH, "...xpath_placeholder...")
    """
    xpath = tab_selector[1].replace('__TAB_NAME__', tab_name)
    btn = wait.until(EC.element_to_be_clickable((tab_selector[0], xpath)))
    btn.click()
    time.sleep(0.7)


def _click_save_button_global(driver, save_btn_selector: tuple, timeout=10):
    """Globalny ZAPISZ (w panelu bocznym/karcie)."""
    try:
        WebDriverWait(driver, timeout).until(EC.element_to_be_clickable(save_btn_selector)).click()
        time.sleep(0.6)
    except Exception:
        pass


# ---- HELPERY DO ROZMIARÓW ----


def _build_sizes_index(menu_json: dict) -> dict:
    """
    Zwraca mapę: { Kategoria: [label_rozmiaru_w_kolejności_JSON], ... }
    bazując na kolejności pojawiania się w menu_json.
    """
    out = {}
    for cat, dishes in (menu_json or {}).items():
        seen = set()
        ordered = []
        for d in dishes or []:
            vlist = ((d.get('popup_details') or {}).get('variants') or [])
            for v in vlist:
                label = _norm_text(v.get('label') or "")
                if not label or label == "__no_variant__":
                    label = "Domyślny"  # kanonizacja, żeby zachować kolejność także dla __no_variant__
                if label not in seen:
                    seen.add(label)
                    ordered.append(label)
        out[cat] = ordered
    return out


def _create_sizes_for_categories(driver, wait, menu_json, categories, log_func, config):
    """
    Wchodzi w zakładkę 'Rozmiary', dodaje brakujące ROZMIARY (Tylko NAZWY!),
    wraca do 'Dania'.
    """
    sizes_index = _build_sizes_index(menu_json)
    _goto_tab(wait, "Rozmiary", config['SELECTOR_TAB_BUTTON'])

    save_selector = config['SELECTOR_GLOBAL_SAVE_BUTTON']
    cat_card_xpath = config['SELECTOR_SIZE_CATEGORY_CARD'][1]
    add_btn_xpath = config['SELECTOR_SIZE_ADD_BUTTON'][1]
    name_input_css = config['SELECTOR_SIZE_NAME_INPUT'][1]

    for cat in categories:
        needed = sizes_index.get(cat, [])
        if not needed:
            log_func(f"[Rozmiary] Kategoria '{cat}': brak rozmiarów do dodania.")
            continue

        log_func(f"[Rozmiary] Kategoria '{cat}': potrzebne rozmiary: {', '.join(sorted(needed))}")

        # karta kategorii
        card = wait.until(EC.presence_of_element_located((
            By.XPATH, cat_card_xpath.replace('__CATEGORY_NAME__', cat)
        )))

        # rozpoznaj już istniejące nazwy (np. 'Domyślny', wcześniejsze)
        existing = set()
        for el in card.find_elements(By.XPATH,
                                     ".//div[contains(@class,'list-group')]//div[contains(@class,'list-group-item')]//span[normalize-space(text())]"):
            existing.add(_norm_text(el.text))

        # przycisk „Dodaj nowy rozmiar”
        add_btn = card.find_element(By.XPATH, add_btn_xpath)

        for label in needed:
            if _norm_text(label) in existing:
                continue
            try:
                driver.execute_script("arguments[0].scrollIntoView({block:'center'});", add_btn)
                add_btn.click()
                inp = wait.until(EC.visibility_of_element_located((
                    By.CSS_SELECTOR, name_input_css
                )))
                inp.clear()
                inp.send_keys(label)  # << TYLKO NAZWA, ŻADNE CENY
                _click_save_button_global(driver, save_selector, timeout=12)  # zapis panelu bocznego
                time.sleep(0.6)
                existing.add(_norm_text(label))
                log_func(f"[Rozmiary] '{cat}': dodano rozmiar '{label}'")
                _progress_tick(wait._driver)
            except Exception as e:
                log_func(f"[Rozmiary] '{cat}': nie udało się dodać '{label}': {e}")

    _goto_tab(wait, "Dania", config['SELECTOR_TAB_BUTTON'])


def _strip_accents(s: str) -> str:
    if not s: return ""
    return "".join(c for c in unicodedata.normalize("NFD", s) if unicodedata.category(c) != "Mn")


def _add_sizes_to_current_dish(driver, wait, dish: dict, log_func, config):
    """
    W karcie dania:
    - dla każdego wariantu (poza 'Domyślny') kliknij '+' w jego wierszu,
    - wpisz cenę do input[name='price'] w tym wierszu,
    - NIE zapisuj tu karty dania (save robimy wyżej, w upload_menu).
    """
    popup = dish.get('popup_details') or {}
    variants = popup.get('variants') or []
    if not variants:
        return

    def looks_like_default(label: str) -> bool:
        t = (_strip_accents(label or "").casefold())
        return "domysln" in t or t.strip() == "default"

    def find_row_for_label(label_text: str):
        xp = config['SELECTOR_SIZE_ROW_IN_DISH_CARD'][1]
        return wait.until(EC.presence_of_element_located(
            (By.XPATH, xp.replace('__LABEL_TEXT__', label_text))
        ))

    def wait_enabled_price_input(row_el, timeout=8):
        end = time.time() + timeout
        last_exc = None
        while time.time() < end:
            try:
                inputs = row_el.find_elements(By.XPATH, config['SELECTOR_SIZE_PRICE_INPUT_IN_ROW'][1])
                inputs = [i for i in inputs if i.is_displayed()]
                if inputs:
                    inp = inputs[-1]
                    disabled_attr = inp.get_attribute("disabled")
                    if (disabled_attr is None or disabled_attr is False) and inp.is_enabled():
                        driver.execute_script("arguments[0].scrollIntoView({block:'center'});", inp)
                        time.sleep(0.05)
                        return inp
                time.sleep(0.12)
            except Exception as e:
                last_exc = e
                time.sleep(0.15)
        if last_exc:
            raise last_exc
        raise Exception("Price input not ready")

    def fill_price(inp_el, value_str: str):
        # 1) normal
        try:
            inp_el.click()
            inp_el.clear()
            inp_el.send_keys(value_str)
            driver.execute_script("arguments[0].dispatchEvent(new Event('input', {bubbles:true}));", inp_el)
            driver.execute_script("arguments[0].dispatchEvent(new Event('change',{bubbles:true}));", inp_el)
            return True
        except Exception:
            pass
        # 2) ActionChains
        try:
            ActionChains(driver).move_to_element(inp_el).click().pause(0.05).send_keys(value_str).perform()
            driver.execute_script("arguments[0].dispatchEvent(new Event('input', {bubbles:true}));", inp_el)
            driver.execute_script("arguments[0].dispatchEvent(new Event('change',{bubbles:true}));", inp_el)
            return True
        except Exception:
            pass
        # 3) JS setter + eventy
        try:
            driver.execute_script("""
                const el = arguments[0], val = arguments[1];
                const d = Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, 'value');
                d.set.call(el, val);
                el.dispatchEvent(new Event('input',  {bubbles:true}));
                el.dispatchEvent(new Event('change', {bubbles:true}));
            """, inp_el, value_str)
            return True
        except Exception:
            return False

    for v in variants:
        label = _norm_text(v.get('label') or '')
        if not label or label == "__no_variant__":
            continue
        if looks_like_default(label):
            log_func(f"   [Rozmiar] '{label}': pomijam (domyślny).")
            continue

        price = v.get('price')
        if price is None:
            price = _price_to_float(v.get('price_text'))
        if price is None:
            log_func(f"   [Rozmiar] '{label}': brak ceny → pomijam.")
            continue

        # wiersz rozmiaru
        try:
            row = find_row_for_label(label)
        except Exception:
            log_func(f"   [Rozmiar] '{label}': nie znaleziono wiersza rozmiaru.")
            continue

        # jeśli nie istnieje, kliknij '+'
        try:
            cls = (row.get_attribute("class") or "")
            if "meal-size-list-item--no-exist" in cls:
                plus = row.find_element(By.XPATH, config['SELECTOR_SIZE_ADD_TO_DISH_BUTTON'][1])
                driver.execute_script("arguments[0].scrollIntoView({block:'center'});", plus)
                driver.execute_script("arguments[0].click();", plus)
                time.sleep(0.25)
                row = find_row_for_label(label)  # odśwież referencję
        except Exception:
            pass

        # input ceny
        try:
            price_input = wait_enabled_price_input(row, timeout=10)
        except Exception as e:
            log_func(f"   [Rozmiar] '{label}': nie udało się znaleźć aktywnego inputa na cenę: {e}")
            continue

        value_str = str(price).replace(',', '.')
        ok = fill_price(price_input, value_str)
        if ok:
            log_func(f"   [Rozmiar] '{label}': ustawiono cenę {value_str}")
            _progress_tick(driver)
        else:
            log_func(f"   [Rozmiar] '{label}': nie udało się wpisać ceny (fallbacky zawiodły)")


def _is_default_label(label: str) -> bool:
    t = _strip_accents(label or "").casefold().strip()
    # akceptuj: "Domyślny", "domyślny", "default" itp.
    return "domysln" in t or t == "default"


def _has_non_default_variants(dish: dict) -> bool:
    vlist = ((dish.get('popup_details') or {}).get('variants') or [])
    for v in vlist:
        lab = _norm_text(v.get('label') or "")
        if lab and lab != "__no_variant__" and not _is_default_label(lab):
            return True
    return False


def _get_default_price_from_dish(dish: dict):
    # 1) najpierw spróbuj z pola 'price' dania
    if dish.get('price') not in (None, ""):
        try:
            return float(str(dish['price']).replace(",", ".").replace(" zł", "").strip())
        except Exception:
            pass
    # 2) jeśli brak, spróbuj znaleźć wariant "Domyślny"
    vlist = ((dish.get('popup_details') or {}).get('variants') or [])
    for v in vlist:
        lab = _norm_text(v.get('label') or "")
        if _is_default_label(lab):
            if v.get('price') not in (None, ""):
                try:
                    return float(str(v['price']).replace(",", "."))
                except Exception:
                    pass
            return _price_to_float(v.get('price_text') or "")
    return None


##DODATKI HELPERY:
def _label_key(s: str) -> str:
    t = _norm_text(s or "")
    t = t.replace(".", "")  # ignoruj kropki typu "ok. 30 cm" vs "ok 30 cm"
    t = t.replace("  ", " ").strip().casefold()
    return t


def _labels_equal(a: str, b: str) -> bool:
    return _label_key(a) == _label_key(b)


def _open_category_by_name(driver, wait, category_name: str, log_func, config):
    want = _norm_text(category_name)
    xpath_template = config['SELECTOR_CATEGORY_ROW'][1]

    # Spróbuj szybkim XPATH
    el = None
    try:
        el = wait.until(EC.element_to_be_clickable((
            By.XPATH, xpath_template.replace('__CATEGORY_NAME__', category_name)
        )))
    except Exception:
        # Iteruj po widocznych i porównaj po _norm_text
        rows = wait.until(EC.presence_of_all_elements_located((
            By.XPATH, "//div[contains(@class,'list-group-item') and .//span]"  # to jest dość ogólny selektor
        )))
        for r in rows:
            try:
                sp = r.find_element(By.XPATH, ".//span[normalize-space(.)]")
                if _norm_text(sp.text) == want:
                    el = r
                    break
            except Exception:
                continue

    if el is None:
        raise Exception(f"Nie znaleziono kategorii (po _norm_text): '{category_name}'")

    try:
        driver.execute_script("arguments[0].scrollIntoView({block:'center'});", el)
    except Exception:
        pass
    try:
        el.click()
    except Exception:
        driver.execute_script("arguments[0].click();", el)
    time.sleep(0.5)

    # Potwierdzenie wejścia: ‘Wróć’ + ‘Dodaj danie’
    wait.until(EC.visibility_of_element_located(config['SELECTOR_BACK_BUTTON']))
    wait.until(EC.visibility_of_element_located(config['SELECTOR_ADD_DISH_BUTTON_IN_CAT']))


# ---- BUDOWANIE PLANU GRUP DODATKÓW (tylko multi_choice_group) ----


def _build_addons_plan_from_menu(menu: dict, log_func, selected_groups: list = None):
    key_map = OrderedDict()  # klucz -> plan, zachowujemy kolejność pierwszego trafienia

    for cat, dishes in (menu or {}).items():
        for dish in dishes or []:
            name = _norm_text(dish.get('name'))
            variants = (((dish.get('popup_details') or {}).get('variants')) or [])
            for v in variants:
                raw_label = v.get('label')
                size_label = _canon_size_label(raw_label)  # "__no_variant__" -> "Domyślny"
                if not size_label:
                    continue

                for g in (v.get('groups') or []):
                    if (g.get('group') != 'multi_choice_group') and (g.get('type') != 'multi'):
                        continue
                    gname = _norm_text(g.get('group_name') or "")
                    if not gname:
                        continue

                    # Przygotuj obiekt do generowania unique_title dla filtrowania
                    temp_choices = []
                    for ch in (g.get('choices') or []):
                        nm = _norm_text(ch.get('name') or "")
                        if nm:
                            pr = ch.get('price', None)
                            if pr is None:
                                pr = _price_to_float(ch.get('price_text') or "")
                            temp_choices.append({'name': nm, 'price': pr})

                    if temp_choices:
                        temp_item = {
                            'group_name': gname,
                            'size_label': size_label,
                            'required': False,  # dla dodatków zawsze False
                            'choices': temp_choices,
                            'targets': {cat: {size_label: {name}}}
                        }
                        unique_title = _unique_group_title(temp_item, 'add')

                        # Filtruj według wybranych grup (porównuj unique_title)
                        if selected_groups is not None and unique_title not in selected_groups:
                            continue

                    # choices w KOLEJNOŚCI z JSON-a
                    choices = []
                    for ch in (g.get('choices') or []):
                        nm = _norm_text(ch.get('name') or "")
                        if not nm:
                            continue
                        pr = ch.get('price', None)
                        if pr is None:
                            pr = _price_to_float(ch.get('price_text') or "")
                        else:
                            try:
                                pr = float(str(pr).replace(",", "."))
                            except Exception:
                                pr = _price_to_float(str(pr))
                        choices.append({'name': nm, 'price': pr})

                    if not choices:
                        continue

                    # klucz deduplikacji (choices_key tylko do porównań, nie do kolejności!)
                    choices_key = tuple(sorted((c['name'], c['price']) for c in choices))
                    key = (_label_key(gname), _label_key(size_label), choices_key)

                    if key not in key_map:
                        key_map[key] = {
                            'title': f"{gname} — {size_label}",
                            'group_name': gname,
                            'size_label': size_label,
                            'choices': choices,  # kolejność z JSON
                            'targets': OrderedDict()  # też zachowamy kolejność kategorii
                        }

                    key_map[key]['targets'].setdefault(cat, OrderedDict()).setdefault(size_label, set()).add(name)

    plan = list(key_map.values())  # BEZ sortowania — kolejność = pierwsze wystąpienie w JSON
    log_func(f"[Dodatki] Zbudowano plan {len(plan)} unikalnych grup (po deduplikacji).")
    return plan


def _build_modifiers_plan_from_menu(menu: dict, log_func, selected_groups: list = None):
    """
    Buduje plan grup single-choice ('Modyfikatory') z JSON-a.
    Deduplikacja po (group_name, size_label, choices, required).
    """
    key_map = OrderedDict()

    def _is_single_group(g: dict) -> bool:
        gname = (g or {}).get('group', '') or ''
        gtype = (g or {}).get('type', '') or ''
        # Akceptuj zarówno poprawne 'single_choice_group', jak i literówkę 'single_choice_grup'
        return (_norm_text(gname) in ('single_choice_group', 'single_choice_grup')) or (_norm_text(gtype) == 'single')

    for cat, dishes in (menu or {}).items():
        for dish in dishes or []:
            variants = (((dish.get('popup_details') or {}).get('variants')) or [])
            for v in variants:
                size_label = _canon_size_label(v.get('label'))
                if not size_label:
                    continue

                for g in (v.get('groups') or []):
                    if not _is_single_group(g):
                        continue

                    group_name = _norm_text(g.get('group_name') or "")
                    if not group_name:
                        continue

                    required = bool(g.get('required', False))

                    # Przygotuj choices dla unique_title
                    temp_choices = []
                    for ch in (g.get('choices') or []):
                        nm = _norm_text(ch.get('name') or "")
                        if nm:
                            pr = ch.get('price', None)
                            if pr is None:
                                pr = _price_to_float(ch.get('price_text') or "")
                            temp_choices.append({'name': nm, 'price': pr})

                    if temp_choices:
                        temp_item = {
                            'group_name': group_name,
                            'size_label': size_label,
                            'required': required,
                            'choices': temp_choices,
                            'targets': {cat: {size_label: {_norm_text(dish.get('name', ''))}}}
                        }
                        unique_title = _unique_group_title(temp_item, 'mod')

                        # Filtruj według wybranych grup (porównuj unique_title)
                        if selected_groups is not None and unique_title not in selected_groups:
                            continue

                    # choices – zachowaj kolejność z JSON
                    choices = []
                    for ch in (g.get('choices') or []):
                        nm = _norm_text(ch.get('name') or "")
                        if not nm:
                            continue
                        pr = ch.get('price', None)
                        if pr is None:
                            pr = _price_to_float(ch.get('price_text') or "")
                        else:
                            try:
                                pr = float(str(pr).replace(",", "."))
                            except Exception:
                                pr = _price_to_float(str(pr))
                        choices.append({'name': nm, 'price': pr})

                    if not choices:
                        continue

                    # klucz deduplikacji – wliczamy 'required', żeby nie mieszać grup różniących się wymagalnością
                    choices_key = tuple(sorted((c['name'], c['price']) for c in choices))
                    key = (_label_key(group_name), _label_key(size_label), choices_key, required)

                    if key not in key_map:
                        key_map[key] = {
                            'title': f"{group_name} — {size_label}",
                            'group_name': group_name,
                            'size_label': size_label,
                            'choices': choices,  # kolejność jak w JSON
                            'required': required,  # nowość
                            'targets': OrderedDict()
                        }

                    key_map[key]['targets'].setdefault(cat, OrderedDict()).setdefault(size_label, set()).add(
                        _norm_text(dish.get('name') or ""))

    plan = list(key_map.values())
    log_func(f"[Modyfikatory] Zbudowano plan {len(plan)} unikalnych grup (single-choice).")
    return plan


def _find_category_row(wait, category_name: str, config):
    xpath_template = config['SELECTOR_CATEGORY_ROW'][1]
    # 1) match 1:1 po normalize-space
    try:
        return wait.until(EC.element_to_be_clickable((
            By.XPATH,
            xpath_template.replace('__CATEGORY_NAME__', _norm_text(category_name))
        )))
    except Exception:
        pass
    # 2) fallback: lekko luźniejszy (gdy UI ma np. NBSP albo dodatkowe spacje)
    return wait.until(EC.element_to_be_clickable((
        By.XPATH,
        f"//div[contains(@class,'list-group-item') and .//span[contains(normalize-space(.), '{_norm_text(category_name)}')]]"
    )))


# ---- HELPERY UI: zakładka „Dodatki” i tworzenie grupy ----
def _open_addons_tab(wait, config, log_func=None):
    from selenium.common.exceptions import TimeoutException
    if _PHASE != "addons":
        if log_func: log_func("[GUARD] Ignoruję wejście w 'Dodatki' (phase != addons)")
        return
    if log_func: log_func("[Dodatki] Przechodzę do zakładki 'Dodatki'…")
    _goto_tab(wait, "Dodatki", config['SELECTOR_TAB_BUTTON'])
    try:
        wait.until(EC.presence_of_element_located(config['SELECTOR_ADD_GROUP_BUTTON']))
        if log_func: log_func("[Dodatki] Zakładka 'Dodatki' gotowa.")
    except TimeoutException as e:
        if log_func: log_func(f"[Dodatki] ⚠ Nie widzę 'Dodaj grupę': {e}")


def _click_add_new_addon(driver, wait, config, log_func=None):
    btn = wait.until(EC.element_to_be_clickable(config['SELECTOR_ADD_ENTRY_BUTTON']))
    before_names = len(
        [e for e in driver.find_elements(By.CSS_SELECTOR, config['SELECTOR_ADDON_NAME_INPUT'][1]) if e.is_displayed()])
    before_prices = len(
        [e for e in driver.find_elements(By.CSS_SELECTOR, config['SELECTOR_ADDON_PRICE_INPUT'][1]) if e.is_displayed()])
    if log_func:
        log_func(f"[Dodatki] Klikam 'Dodaj ' (entryName: {before_names}, price: {before_prices})")
    try:
        _dbg_highlight(driver, btn)
        btn.click()
    except Exception as e:
        if log_func: log_func(f"[Dodatki] click() nieudany ({e}); próbuję JS click…")
        driver.execute_script("arguments[0].click();", btn)

    time.sleep(0.15)
    # czekamy aż przybędzie co najmniej jeden entryName LUB price
    wait.until(lambda d: (
            len([e for e in d.find_elements(By.CSS_SELECTOR, config['SELECTOR_ADDON_NAME_INPUT'][1]) if
                 e.is_displayed()]) > before_names
            or
            len([e for e in d.find_elements(By.CSS_SELECTOR, config['SELECTOR_ADDON_PRICE_INPUT'][1]) if
                 e.is_displayed()]) > before_prices
    ))
    after_names = len(
        [e for e in driver.find_elements(By.CSS_SELECTOR, config['SELECTOR_ADDON_NAME_INPUT'][1]) if e.is_displayed()])
    after_prices = len([e for e in driver.find_elements(By.CSS_SELECTOR, config['SELECTOR_ADDON_PRICE_INPUT'][1]) if
                        e.is_displayed()])
    if log_func:
        log_func(f"[Dodatki] Po 'Dodaj nowy': entryName={after_names}, price={after_prices}")


def _fill_group_name(driver, wait, title: str, config):
    inp = wait.until(EC.visibility_of_element_located(config['SELECTOR_GROUP_NAME_INPUT']))
    inp.clear();
    inp.send_keys(title)
    time.sleep(0.1)


def _ensure_expanded_section(root_el):
    try:
        btn = root_el.find_element(By.XPATH, ".//button[contains(@class,'collapseButton')]")
        aria = btn.get_attribute("aria-expanded")
        if aria in ("false", None, ""):
            btn.click();
            time.sleep(0.2)
    except Exception:
        pass


def _select_targets_in_meals_tree(driver, wait, targets: dict, log_func, config):
    """
    targets: { category: { size_label: set(dish_names) } }
    Klikamy checkboxy przy daniach we wskazanych kategoriach i rozmiarach.
    """
    # kontener sekcji
    root = wait.until(EC.presence_of_element_located(config['SELECTOR_MEAL_TREE_CONTAINER']))
    targets = {cat: {_canon_size_label(sz): set(dishes) for sz, dishes in sizes.items()} for cat, sizes in
               targets.items()}
    for cat, sizes in targets.items():
        # wiersz kategorii
        cat_row = root.find_element(By.XPATH,
                                    f".//div[contains(@class,'list-group-item')][.//span[normalize-space(text())='{cat}']]")
        _ensure_expanded_section(cat_row)
        # id panelu z rozmiarami dla tej kategorii:
        cat_btn = cat_row.find_element(By.XPATH, ".//button[contains(@class,'collapseButton')]")
        cat_panel_id = cat_btn.get_attribute("aria-controls")
        cat_panel = root.find_element(By.XPATH, f".//div[@id='{cat_panel_id}']")

        for size_label, dish_names in sizes.items():
            # wiersz rozmiaru
            def _find_size_row_in(cat_panel, size_label: str):
                # 1) spróbuj dokładnym XPath (szybko)
                try:
                    return cat_panel.find_element(By.XPATH,
                                                  f".//div[contains(@class,'list-group-item') and .//span[normalize-space(text())='{size_label}']]"
                                                  )
                except Exception:
                    pass
                # 2) iteruj po wszystkich wierszach rozmiarów i porównaj kanonicznie
                rows = cat_panel.find_elements(By.XPATH,
                                               ".//div[contains(@class,'list-group-item') and .//div[contains(@class,'groupCheckbox')]]")
                for r in rows:
                    try:
                        span = r.find_element(By.XPATH, ".//span[normalize-space(text())]")
                        txt = _norm_text(span.text)
                        if _labels_equal(txt, size_label) or (
                                _labels_equal(size_label, "Domyślny") and "domyśln" in _strip_accents(txt).casefold()):
                            return r
                    except Exception:
                        continue
                raise Exception(f"Nie znaleziono rozmiaru '{size_label}' w tej kategorii")

            size_row = _find_size_row_in(cat_panel, size_label)
            _ensure_expanded_section(size_row)
            size_btn = size_row.find_element(By.XPATH, ".//button[contains(@class,'collapseButton')]")
            size_panel_id = size_btn.get_attribute("aria-controls")
            size_panel = cat_panel.find_element(By.XPATH, f".//div[@id='{size_panel_id}']")

            # zaznacz poszczególne dania (label z tekstem = nazwa dania)
            for dish in sorted(dish_names):
                try:
                    lbl = size_panel.find_element(By.XPATH,
                                                  f".//label[contains(@class,'custom-control-label') and normalize-space(text())='{dish}']")
                    driver.execute_script("arguments[0].scrollIntoView({block:'center'});", lbl)
                    lbl.click()
                    time.sleep(0.05)
                    log_func(f"[Dodatki] ✓ Przypięto grupę do dania: {cat} / {size_label} / {dish}")
                except Exception as e:
                    log_func(f"[Dodatki] ⚠ Nie znaleziono dania: {cat} / {size_label} / {dish} ({e})")


def _open_group_from_left_list(driver, wait, title: str):
    # Szukaj klikalnego wiersza listy, który zawiera naszą unikalną nazwę (title)
    item = wait.until(EC.element_to_be_clickable((
        By.XPATH,
        f"//div[contains(@class,'list-group-item')][.//div[contains(@class,'font-weight-medium') and contains(normalize-space(text()), '{title}')]]"
    )))
    # Używamy JS do scrollowania i klikania na wszelki wypadek
    driver.execute_script("arguments[0].scrollIntoView({block:'center'});", item)
    try:
        item.click()
    except Exception:
        driver.execute_script("arguments[0].click();", item)
    time.sleep(0.4)


def _switch_to_group_addons_tab(wait, config, log_func=None):
    if _PHASE != "addons":
        if log_func: log_func("[GUARD] Ignoruję przełączenie na kartę 'Dodatki' (phase != addons)")
        return
    if log_func: log_func("[Dodatki] Przełączam na kartę 'Dodatki'…")
    tab = wait.until(EC.element_to_be_clickable(config['SELECTOR_GROUP_DETAILS_TAB_ADDONS']))
    try:
        tab.click()
    except Exception:
        wait._driver.execute_script("arguments[0].click();", tab)
    time.sleep(0.2)


def _fill_and_save_last_addon_row(driver, wait, name: str, price, config, log_func=None, max_retries=2):
    name_input_css = config['SELECTOR_ADDON_NAME_INPUT'][1]
    price_input_css = config['SELECTOR_ADDON_PRICE_INPUT'][1]
    save_row_xpath = config['SELECTOR_ADDON_SAVE_ROW_BUTTON'][1]

    for attempt in range(1, max_retries + 1):
        try:
            # OSTATNI WIDOCZNY entryName
            names = [e for e in driver.find_elements(By.CSS_SELECTOR, name_input_css) if e.is_displayed()]
            if not names:
                raise Exception("Brak widocznych inputów entryName po 'Dodaj nowy'")
            name_inp = names[-1]
            _dbg_highlight(driver, name_inp, "deepskyblue")
            driver.execute_script("arguments[0].scrollIntoView({block:'center'});", name_inp)

            # Kontener wiersza (najbliższy .list-group-item; fallback: parentNode chain)
            row = driver.execute_script("""
                const el = arguments[0];
                return el.closest('.list-group-item') || el.closest('.d-flex') || el.closest('div');
            """, name_inp)
            if row is None:
                # fallback: użyj parenta z Pythona
                row = name_inp.find_element(By.XPATH, "./ancestor::div[1]")

            _dbg_highlight(driver, row, "orange")

            # NAZWA
            name_inp.clear();
            name_inp.send_keys(name)
            vname = name_inp.get_attribute("value")
            if log_func: log_func(f"[Dodatki] → nazwa='{name}' (w polu: '{vname}')")

            # CENA (opcjonalnie – puste jeśli None)
            price_inps = [e for e in row.find_elements(By.CSS_SELECTOR, price_input_css) if e.is_displayed()]
            if not price_inps:
                # fallback: ostatni widoczny 'price' globalnie
                price_inps = [e for e in driver.find_elements(By.CSS_SELECTOR, price_input_css) if
                              e.is_displayed()]
            vprice = "<none>"
            if price_inps:
                price_inp = price_inps[-1]
                _dbg_highlight(driver, price_inp, "gold")
                driver.execute_script("arguments[0].scrollIntoView({block:'center'});", price_inp)
                price_inp.clear()
                if price is not None:
                    price_inp.send_keys(str(price).replace(",", "."))
                vprice = price_inp.get_attribute("value")
            if log_func: log_func(f"[Dodatki] → cena='{vprice}' (None => puste)")

            # ZAPIS
            save_btns = row.find_elements(By.XPATH, save_row_xpath)
            if not save_btns:
                # fallback globalny
                save_btns = driver.find_elements(By.XPATH, save_row_xpath)
            if not save_btns:
                raise Exception("Nie znalazłem zielonego przycisku 'Zapisz' w wierszu")

            save_btn = save_btns[-1]
            _dbg_highlight(driver, save_btn, "lime")
            driver.execute_script("arguments[0].scrollIntoView({block:'center'});", save_btn)
            if log_func: log_func("[Dodatki] Klikam 'Zapisz' w wierszu…")
            try:
                save_btn.click()
            except Exception as e:
                if log_func: log_func(f"[Dodatki] save click() nieudany ({e}); próbuję JS click…")
                driver.execute_script("arguments[0].click();", save_btn)

            # POTWIERDZENIE ZAPISU
            ok = False
            try:
                WebDriverWait(driver, 5).until(EC.staleness_of(save_btn))
                ok = True
                if log_func: log_func("[Dodatki] Zapis OK (staleness).")
            except Exception:
                time.sleep(0.3)
                still = row.find_elements(By.XPATH, save_row_xpath)
                if not still:
                    ok = True
                    if log_func: log_func("[Dodatki] Zapis OK (przycisk zniknął).")

            if not ok:
                if log_func:
                    log_func("[Dodatki] ⚠ Brak potwierdzenia zapisu – stan widocznych wierszy:")
                    _debug_dump_visible_addon_rows(driver, log_func)
                raise Exception("Brak potwierdzenia zapisu")

            return True

        except Exception as e:
            if log_func: log_func(f"[Dodatki] Próba {attempt}/{max_retries} nieudana: {e}")
            time.sleep(0.5)

    if log_func:
        log_func(f"[Dodatki] ❌ Nie udało się zapisać pozycji: '{name}' @ {price}")
        _debug_dump_visible_addon_rows(driver, log_func)
    return False


def _click_add_new_group(wait, config, log_func=None):
    # dostępne w fazie dodatków i modyfikatorów
    if _PHASE not in ("addons", "modifiers"):
        if log_func: log_func(f"[GUARD] Ignoruję 'Dodaj grupę' (phase = {_PHASE})")
        return

    btn_selector = config['SELECTOR_ADD_GROUP_BUTTON']

    btn = None
    try:
        btn = wait.until(EC.element_to_be_clickable(btn_selector))
        if btn:
            pass
    except Exception:
        # Fallback na XPATH
        xpaths = [
            # 1) dokładnie to co podałeś – przycisk z tekstem
            "//button[contains(@class,'btn-primary') and contains(@class,'btn-sm') and contains(normalize-space(.), 'Dodaj grupę')]",
            # 2) wersja oparta o ikonkę plusa
            "//button[contains(@class,'btn-primary') and contains(@class,'btn-sm') and .//i[contains(@class,'fa-plus-square')]]",
            # 3) awaryjnie: każdy primary+sm w widoku (klikniemy pierwszy widoczny)
            "(//button[contains(@class,'btn-primary') and contains(@class,'btn-sm')])[1]",
        ]
        for xp in xpaths:
            try:
                btn = wait.until(EC.element_to_be_clickable((By.XPATH, xp)))
                if btn: break
            except Exception:
                continue

    if btn is None:
        raise Exception("Nie znalazłem przycisku 'Dodaj grupę' w tej zakładce")

    try:
        _dbg_highlight(wait._driver, btn)
        wait._driver.execute_script("arguments[0].scrollIntoView({block:'center'});", btn)
    except Exception:
        pass

    try:
        btn.click()
    except Exception:
        wait._driver.execute_script("arguments[0].click();", btn)

    # potwierdź pojawienie się pola nazwy grupy
    wait.until(EC.visibility_of_element_located(config['SELECTOR_GROUP_NAME_INPUT']))


def _reset_addon_group_context(wait, config, log_func=None):
    try:
        if log_func: log_func("[Dodatki] Reset kontekstu: przejście Rozmiary → Dodatki…")
        _goto_tab(wait, "Rozmiary", config['SELECTOR_TAB_BUTTON'])
        time.sleep(0.4)
    except Exception as e:
        if log_func: log_func(f"[Dodatki] ⚠ Nie udało się wejść w 'Rozmiary': {e}")
    try:
        _goto_tab(wait, "Dodatki", config['SELECTOR_TAB_BUTTON'])
        time.sleep(0.4)
        # upewnij się, że jesteśmy na liście grup (widać „Dodaj grupę")
        wait.until(EC.presence_of_element_located(config['SELECTOR_ADD_GROUP_BUTTON']))
        if log_func: log_func("[Dodatki] Reset OK — mam przycisk 'Dodaj grupę'.")
    except Exception as e:
        if log_func: log_func(f"[Dodatki] ⚠ Po resecie nie widzę 'Dodaj grupę': {e}")


def _apply_addons_plan(driver, wait, plan: list, log_func, config):
    global _ADDONS_RAN
    if _PHASE != "addons":
        if log_func: log_func("[GUARD] _apply_addons_plan wywołane poza fazą 'addons' — ignoruję.")
        return
    if _ADDONS_RAN:
        if log_func: log_func("[GUARD] Dodatki już były uruchomione — pomijam (idempotencja).")
        return
    _ADDONS_RAN = True

    _open_addons_tab(wait, config, log_func=log_func)
    save_selector = config['SELECTOR_GLOBAL_SAVE_BUTTON']

    for i, item in enumerate(plan, start=1):
        base_title = item['title']
        title = _unique_group_title(item, kind="add")

        # ——— KLUCZOWE: twardy reset między grupami ———
        if i > 1:
            _reset_addon_group_context(wait, config, log_func=log_func)

        log_func(f"[Dodatki] ({i}/{len(plan)}) Tworzę/otwieram grupę: {base_title}  →  {title}")

        if _group_exists_in_left_list(wait, title):
            _open_group_from_left_list(driver, wait, title)
            _switch_to_group_addons_tab(wait, config, log_func=log_func)
        else:
            # 2) Nowa grupa + nazwa
            _click_add_new_group(wait, config, log_func=log_func)
            _fill_group_name(driver, wait, title, config)

            # 3) Przypięcie do dań
            tcount = sum(len(dishes) for sizes in item['targets'].values() for dishes in sizes.values())
            log_func(f"[Dodatki] Przypinam do {tcount} dań…")
            _select_targets_in_meals_tree(driver, wait, item['targets'], log_func, config)

            # 4) Zapis grupy
            _click_save_button_global(driver, save_selector, timeout=12);
            time.sleep(0.5)

            # 5) Otwórz grupę z lewej listy → karta „Dodatki”
            _open_group_from_left_list(driver, wait, title)
            _switch_to_group_addons_tab(wait, config, log_func=log_func)

        # 6) Dodaj pozycje (name, price)
        log_func(f"[Dodatki] Dodaję {len(item['choices'])} pozycji…")
        for idx, ch in enumerate(item['choices'], start=1):
            log_func(f"[Dodatki]  • ({idx}/{len(item['choices'])}) '{ch['name']}' @ {ch['price']}")
            _click_add_new_addon(driver, wait, config, log_func=log_func)
            _fill_and_save_last_addon_row(driver, wait, ch['name'], ch['price'], config, log_func=log_func)
            _progress_tick(driver)


def _canon_size_label(raw: str) -> str:
    """Zamień pusty/__no_variant__ na 'Domyślny', resztę normalizuj."""
    t = _norm_text(raw or "")
    if not t or t == "__no_variant__":
        return "Domyślny"
    return t


# helpery modyfikatory
def _open_modifiers_tab(wait, config, log_func=None):
    if _PHASE != "modifiers":
        if log_func: log_func("[GUARD] Ignoruję wejście w 'Modyfikatory' (phase != modifiers)")
        return
    if log_func: log_func("[Modyfikatory] Przechodzę do zakładki 'Modyfikatory'…")
    _goto_tab(wait, "Modyfikatory", config['SELECTOR_TAB_BUTTON'])
    wait.until(EC.presence_of_element_located(config['SELECTOR_ADD_GROUP_BUTTON']))
    if log_func: log_func("[Modyfikatory] Zakładka gotowa.")


def _switch_to_group_modifiers_tab(wait, config, log_func=None):
    if _PHASE != "modifiers":
        if log_func: log_func("[GUARD] Ignoruję przełączenie na kartę 'Modyfikatory' (phase != modifiers)")
        return
    if log_func: log_func("[Modyfikatory] Przełączam kartę na 'Modyfikatory'…")
    tab = wait.until(EC.element_to_be_clickable(config['SELECTOR_GROUP_DETAILS_TAB_MODIFIERS']))
    try:
        tab.click()
    except Exception:
        wait._driver.execute_script("arguments[0].click();", tab)
    time.sleep(0.2)


def _reset_modifier_group_context(wait, config, log_func=None):
    try:
        if log_func: log_func("[Modyfikatory] Reset: Rozmiary → Modyfikatory…")
        _goto_tab(wait, "Rozmiary", config['SELECTOR_TAB_BUTTON']);
        time.sleep(0.3)
    except Exception as e:
        if log_func: log_func(f"[Modyfikatory] ⚠ Nie udało się wejść w 'Rozmiary': {e}")
    try:
        _goto_tab(wait, "Modyfikatory", config['SELECTOR_TAB_BUTTON']);
        time.sleep(0.3)
        wait.until(EC.presence_of_element_located(config['SELECTOR_ADD_GROUP_BUTTON']))
        if log_func: log_func("[Modyfikatory] Reset OK.")
    except Exception as e:
        if log_func: log_func(f"[Modyfikatory] ⚠ Po resecie nie widzę listy grup: {e}")


def _set_group_required_toggle(driver, wait, required: bool, config, log_func=None):
    try:
        root = wait.until(EC.presence_of_element_located(config['SELECTOR_REQUIRED_TOGGLE_CONTAINER']))
        # checkbox w środku label.switch
        chk = root.find_element(By.XPATH, config['SELECTOR_REQUIRED_TOGGLE_CHECKBOX'][1])
        is_on = chk.is_selected()
        if (required and not is_on) or ((not required) and is_on):
            lbl = root.find_element(By.XPATH, config['SELECTOR_REQUIRED_TOGGLE_LABEL'][1])
            try:
                lbl.click()
            except Exception:
                driver.execute_script("arguments[0].click();", lbl)
            time.sleep(0.1)
            if log_func: log_func(f"[Modyfikatory] 'Wymagana' → {'TAK' if required else 'NIE'}")
    except Exception as e:
        if log_func: log_func(f"[Modyfikatory] ⚠ Nie ustawiono 'Wymagana': {e}")


def _apply_modifiers_plan(driver, wait, plan: list, log_func, config):
    global _MODIFIERS_RAN
    if _PHASE != "modifiers":
        if log_func: log_func("[GUARD] _apply_modifiers_plan poza fazą 'modifiers' — ignoruję.")
        return
    if _MODIFIERS_RAN:
        if log_func: log_func("[GUARD] Modyfikatory już były uruchomione — pomijam.")
        return
    _MODIFIERS_RAN = True

    _open_modifiers_tab(wait, config, log_func=log_func)
    save_selector = config['SELECTOR_GLOBAL_SAVE_BUTTON']

    for i, item in enumerate(plan, start=1):
        base_title = item['title']
        title = _unique_group_title(item, kind="mod")
        required = bool(item.get('required', False))

        if i > 1:
            _reset_modifier_group_context(wait, config, log_func=log_func)

        log_func(f"[Modyfikatory] ({i}/{len(plan)}) Tworzę/otwieram grupę: {base_title}  →  {title}")

        if _group_exists_in_left_list(wait, title):
            # Istnieje – otwórz, ustaw 'Wymagana' i przejdź do karty 'Modyfikatory'
            _open_group_from_left_list(driver, wait, title)
            _set_group_required_toggle(driver, wait, required, config, log_func=log_func)
            _click_save_button_global(driver, save_selector, timeout=12);
            time.sleep(0.3)
            _switch_to_group_modifiers_tab(wait, config, log_func=log_func)
        else:
            # 1) nowa grupa + nazwa
            _click_add_new_group(wait, config, log_func=log_func)  # reuse z Dodatków (po poprawce guardu)
            _fill_group_name(driver, wait, title, config)

            # 2) toggle 'Wymagana' z JSON
            _set_group_required_toggle(driver, wait, required, config, log_func=log_func)

            # 3) przypięcie do dań/rozmiarów
            tcount = sum(len(dishes) for sizes in item['targets'].values() for dishes in sizes.values())
            log_func(f"[Modyfikatory] Przypinam do {tcount} dań…")
            _select_targets_in_meals_tree(driver, wait, item['targets'], log_func, config)

            # 4) zapis grupy
            _click_save_button_global(driver, save_selector, timeout=12);
            time.sleep(0.4)

            # 5) otwarcie z lewej listy i wejście w kartę 'Modyfikatory'
            _open_group_from_left_list(driver, wait, title)
            _switch_to_group_modifiers_tab(wait, config, log_func=log_func)

        # 6) pozycje (jak w Dodatkach)
        log_func(f"[Modyfikatory] Dodaję {len(item['choices'])} pozycji…")
        for idx, ch in enumerate(item['choices'], start=1):
            log_func(f"[Modyfikatory]  • ({idx}/{len(item['choices'])}) '{ch['name']}' @ {ch['price']}")
            _click_add_new_addon(driver, wait, config, log_func=log_func)  # reuse
            _fill_and_save_last_addon_row(driver, wait, ch['name'], ch['price'], config, log_func=log_func)
            _progress_tick(driver)



# --- ZMIENNE GLOBALNE (Wklej zaraz pod importami) ---
# 1. Słownik postępu (To naprawi Twój błąd)
_PROGRESS = {"total": 0, "done": 0, "t0": None, "est_total": 0.0, "callback": None}

_PHASE = "start" # Startowa faza
_PHASE_START_TIME = time.time()
_PHASE_HISTORY = {} # Tu trzymamy czasy zakończonych faz

_PHASE_MAP = {
    "start":       {"label": "Start",     "icon": "🚀", "est_per_item": 0},
    "categories":  {"label": "Kategorie", "icon": "📂", "est_per_item": 1.5},
    "sizes":       {"label": "Rozmiary",  "icon": "📏", "est_per_item": 1.0},
    "dishes":      {"label": "Dania",     "icon": "🍕", "est_per_item": 4.5}, # Dania + Składniki
    "addons":      {"label": "Dodatki",   "icon": "🍟", "est_per_item": 5.0},
    "modifiers":   {"label": "Modyfik.",  "icon": "⚙️", "est_per_item": 5.0},
    "done":        {"label": "Gotowe",    "icon": "🏁", "est_per_item": 0},
    "ingredients": {"label": "Składniki", "icon": "🍅", "est_per_item": 1.0}
}

# Kolejność na pasku Steppera (bez ingredients!)
_PHASE_ORDER = ["categories", "sizes", "dishes", "addons", "modifiers"]

_PHASE_COUNTS = {k: 0 for k in _PHASE_MAP.keys()}
_PHASE_TOTALS = {
    "categories": 0, "dishes": 0, "sizes": 0,
    "addons": 0, "modifiers": 0, "ingredients": 0
}



def _progress_eta_str(seconds: float) -> str:
    s = max(0, int(seconds))
    m, s = divmod(s, 60);
    h, m = divmod(m, 60)
    return f"{h}h {m}m {s}s" if h else (f"{m}m {s}s" if m else f"{s}s")


def _progress_init(driver, total_steps: int, est_seconds: float, progress_callback=None):
    global _PHASE_COUNTS
    _PROGRESS.update(total=total_steps, done=0, t0=time.time(), est_total=est_seconds, callback=progress_callback)

    # Synchronizacja liczników
    try:
        for k in _PHASE_COUNTS.keys():
            if k in _PHASE_TOTALS: _PHASE_COUNTS[k] = _PHASE_TOTALS[k]
    except:
        pass

    ing_count = _PHASE_COUNTS.get('ingredients', 0)
    dish_count = _PHASE_COUNTS.get('dishes', 0)
    total_dish_est = (dish_count * _PHASE_MAP['dishes']['est_per_item']) + (
                ing_count * _PHASE_MAP['ingredients']['est_per_item'])

    # Generowanie Kafelków
    history_html = ""
    for p_key in _PHASE_ORDER:
        p_info = _PHASE_MAP[p_key]
        seconds = 0
        if p_key == 'dishes':
            seconds = total_dish_est
        else:
            seconds = _PHASE_COUNTS.get(p_key, 0) * p_info['est_per_item']

        if seconds > 0:
            history_html += f"""
            <div id="card-{p_key}" class="papu-card">
                <div class="papu-card-icon" data-orig-icon="{p_info['icon']}">{p_info['icon']}</div>
                <div class="papu-card-info">
                    <span class="papu-card-label">{p_info['label']}</span>
                    <span id="act-{p_key}" class="papu-card-time">--:--</span>
                </div>
            </div>
            """

    phases_json = json.dumps([{"key": k} for k in _PHASE_ORDER])

    js = f"""
    (function(){{
      var navLeft = document.querySelector('.main-nav__left');
      var old = document.getElementById('papu-widget');
      if(old) old.remove();

      var css = `
        /* MAIN CONTAINER - ALWAYS EXPANDED */
        #papu-widget {{
            display: flex;
            align-items: center;
            background: #1e293b;
            border: 1px solid rgba(255,255,255,0.1);
            border-radius: 8px;
            height: 42px;
            margin-left: 15px;
            font-family: 'Segoe UI', sans-serif;
            color: white;
            overflow: hidden;
            white-space: nowrap;
            cursor: default; /* Brak łapki */
            position: relative;
            box-shadow: 0 4px 6px rgba(0,0,0,0.1);
            user-select: none;
            max-width: none; /* Brak limitu szerokości */
            width: auto;
        }}

        /* LEFT SECTION */
        .papu-summary {{
            display: flex;
            align-items: center;
            height: 100%;
            padding: 0 12px;
            min-width: 140px;
            background: rgba(255,255,255,0.02);
            z-index: 2;
            position: relative;
            border-right: 1px solid rgba(255,255,255,0.05);
        }}

        .papu-main-icon {{
            font-size: 20px;
            margin-right: 10px;
            filter: drop-shadow(0 2px 4px rgba(0,0,0,0.2));
        }}

        .papu-text-group {{
            display: flex;
            flex-direction: column;
            justify-content: center;
            line-height: 1.2;
        }}

        .papu-pct-main {{ font-size: 14px; font-weight: 700; color: white; letter-spacing: 0.5px; }}
        .papu-eta-main {{ font-size: 10px; color: #94a3b8; font-weight: 500; }}

        /* PROGRESS BAR (BOTTOM) */
        .papu-progress-track {{
            position: absolute; bottom: 0; left: 0; width: 100%; height: 3px;
            background: rgba(0,0,0,0.2);
        }}
        #papu-progress-fill {{
            height: 100%; width: 0%;
            background: #3b82f6;
            transition: width 0.3s ease;
            box-shadow: 0 0 10px rgba(59, 130, 246, 0.7);
        }}

        /* RIGHT SECTION (DETAILS - ALWAYS VISIBLE) */
        .papu-details {{
            display: flex;
            align-items: center;
            gap: 8px;
            padding: 0 12px;
            opacity: 1; /* Zawsze widoczne */
        }}

        /* PHASE CARDS */
        .papu-card {{
            display: flex; align-items: center; gap: 8px;
            background: rgba(255,255,255,0.05);
            border: 1px solid rgba(255,255,255,0.05);
            border-radius: 6px;
            padding: 4px 8px;
            transition: all 0.2s;
        }}

        .papu-card-icon {{ font-size: 14px; opacity: 0.7; }}

        .papu-card-info {{ display: flex; flex-direction: column; line-height: 1; }}
        .papu-card-label {{ font-size: 9px; text-transform: uppercase; color: #94a3b8; font-weight: 700; margin-bottom: 2px; }}
        .papu-card-time {{ font-size: 11px; color: #cbd5e1; font-family: 'Consolas', monospace; }}

        /* CARD STATES */
        .card-active {{
            background: rgba(59, 130, 246, 0.15);
            border-color: rgba(59, 130, 246, 0.3);
        }}
        .card-active .papu-card-label {{ color: #60a5fa; }}
        .card-active .papu-card-time {{ color: white; font-weight: bold; }}
        .card-active .papu-card-icon {{ opacity: 1; transform: scale(1.1); }}

        .card-done {{
            background: rgba(16, 185, 129, 0.1);
            border-color: rgba(16, 185, 129, 0.2);
        }}
        .card-done .papu-card-label {{ color: #34d399; }}
        .card-done .papu-card-icon {{ color: #34d399; opacity: 1; }}
      `;

      var styleTag = document.createElement('style'); styleTag.innerHTML = css;
      var widget = document.createElement('div'); widget.id = 'papu-widget';
      widget.appendChild(styleTag);

      widget.innerHTML += `
        <div class="papu-summary">
            <div id="papu-main-icon" class="papu-main-icon">🚀</div>
            <div class="papu-text-group">
                <div id="papu-pct" class="papu-pct-main">0%</div>
                <div id="papu-eta" class="papu-eta-main">Start...</div>
            </div>

            <div class="papu-progress-track">
                <div id="papu-progress-fill"></div>
            </div>
        </div>

        <div class="papu-details">
            {history_html}
        </div>
      `;

      if (navLeft) {{
          navLeft.appendChild(widget);
      }} else {{
          document.body.appendChild(widget);
          widget.style.position = 'fixed'; widget.style.top = '10px'; widget.style.left = '10px'; widget.style.zIndex = '9999';
      }}

      // --- UPDATE FUNCTION ---
      window.updatePapuStats = function(pct, eta, detail, currentPhase, phaseActTime) {{
          document.getElementById('papu-pct').textContent = pct + '%';
          document.getElementById('papu-eta').textContent = eta;
          document.getElementById('papu-progress-fill').style.width = pct + '%';

          var phases = {phases_json};
          var foundCurrent = false;

          phases.forEach(p => {{
              var card = document.getElementById('card-' + p.key);
              var timeEl = document.getElementById('act-' + p.key);

              if (!card) return;

              var iconEl = card.querySelector('.papu-card-icon');
              var origIcon = iconEl.getAttribute('data-orig-icon');

              if (p.key === currentPhase) {{
                  document.getElementById('papu-main-icon').textContent = p.icon;
                  card.className = 'papu-card card-active';
                  iconEl.textContent = origIcon;
                  if(timeEl) timeEl.textContent = phaseActTime;
                  foundCurrent = true;

              }} else if (!foundCurrent) {{
                  card.className = 'papu-card card-done';
                  iconEl.textContent = '✓';
              }} else {{
                  card.className = 'papu-card';
                  iconEl.textContent = origIcon;
                  if(timeEl) timeEl.textContent = '--:--';
              }}
          }});
      }};
    }})();
    """
    try:
        driver.execute_script(js)
    except Exception:
        pass


def _progress_tick(driver, n: int = 1, text: str = None):
    global _PHASE, _PHASE_START_TIME, _PHASE_HISTORY
    if not _PROGRESS["t0"]: return

    _PROGRESS["done"] += n
    done = _PROGRESS["done"]
    tot = max(1, _PROGRESS["total"])
    pct = int(done * 100 / tot)

    # Global ETA
    elapsed_global = time.time() - _PROGRESS["t0"]
    avg = elapsed_global / done if done else 0.0
    remaining = avg * (tot - done) if avg > 0 else (_PROGRESS["est_total"] or 0.0)
    eta_str = _progress_eta_str(remaining)

    # Czas trwania AKTUALNEJ fazy
    phase_elapsed = time.time() - _PHASE_START_TIME
    phase_elapsed_str = _progress_eta_str(phase_elapsed).replace("h ", ":").replace("m ", ":").replace("s", "")

    # Wyświetlana faza (składniki udają dania)
    display_phase = "dishes" if _PHASE == "ingredients" else _PHASE
    current_label = _PHASE_MAP.get(display_phase, {}).get("label", display_phase)
    detail_text = text if text else f"[{current_label}] {done}/{tot}"

    # Wstrzykiwanie historii zakończonych faz
    history_js = ""
    for ph, dur in _PHASE_HISTORY.items():
        m, s = divmod(int(dur), 60)
        dur_str = f"{m:02d}:{s:02d}"
        history_js += f"var e=document.getElementById('act-{ph}'); if(e){{e.textContent='{dur_str}'; e.style.color='#10b981';}}"

    js = f"""
    if(window.updatePapuStats) {{
        window.updatePapuStats(arguments[0], arguments[1], arguments[2], arguments[3], arguments[4]);
        {history_js}
    }}
    """
    try:
        driver.execute_script(js, pct, eta_str, detail_text, display_phase, phase_elapsed_str)
    except Exception:
        pass

    if _PROGRESS["callback"]:
        try:
            _PROGRESS["callback"](done, tot, text if text else "", _PHASE)
        except Exception:
            pass


def _progress_compute_totals(menu: dict,
                             skip_categories: bool, skip_dishes: bool,
                             with_desc: bool, with_ing: bool,
                             with_sizes: bool, with_addons: bool, with_modifiers: bool):
    global _PHASE_TOTALS

    categories = list(menu.keys())
    dishes = sum(len(v or []) for v in menu.values())

    # Zliczanie surowych danych z JSON
    sizes_index = _build_sizes_index(menu)
    sizes_to_create = sum(len(v) for v in sizes_index.values())

    non_default_variants = 0
    dishes_with_desc = 0
    total_ingredients = 0

    for arr in (menu or {}).values():
        for d in (arr or []):
            if isinstance(d.get("description"), str) and d["description"].strip():
                dishes_with_desc += 1
            if isinstance(d.get("ingredients"), list):
                total_ingredients += len(d["ingredients"])

            # Warianty
            for v in ((d.get('popup_details') or {}).get('variants') or []):
                lab = _norm_text(v.get('label') or "")
                if lab and lab != "__no_variant__" and not _is_default_label(lab):
                    non_default_variants += 1

    # --- KLUCZOWY MOMENT: ZEROWANIE LICZNIKÓW JEŚLI OPCJA WYŁĄCZONA ---

    # Jeśli skip_categories=True -> 0
    _PHASE_TOTALS["categories"] = len(categories) if not skip_categories else 0

    # Jeśli skip_dishes=True -> 0
    _PHASE_TOTALS["dishes"] = dishes if not skip_dishes else 0

    # Jeśli with_sizes=False -> 0
    _PHASE_TOTALS["sizes"] = (sizes_to_create + non_default_variants) if with_sizes else 0

    # Jeśli with_ing=False -> 0 (TUTAJ JEST POPRAWKA DLA CIEBIE)
    _PHASE_TOTALS["ingredients"] = total_ingredients if (with_ing and not skip_dishes) else 0

    # Dodatki i Modyfikatory
    addons_plan = _build_addons_plan_from_menu(menu, log_func=lambda *a, **k: None)
    modifiers_plan = _build_modifiers_plan_from_menu(menu, log_func=lambda *a, **k: None)

    _PHASE_TOTALS["addons"] = len(addons_plan) if (with_addons) else 0
    _PHASE_TOTALS["modifiers"] = len(modifiers_plan) if (with_modifiers) else 0

    # Obliczanie kroków paska postępu (Total steps)
    steps = 0
    steps += _PHASE_TOTALS["categories"]
    steps += _PHASE_TOTALS["dishes"]
    steps += _PHASE_TOTALS["sizes"]
    if with_desc and not skip_dishes: steps += dishes_with_desc
    steps += _PHASE_TOTALS["ingredients"]  # Doda 0 jeśli wyłączone

    # Dodatki i modyfikatory (liczymy pozycje wewnątrz grup)
    if with_addons: steps += sum(len(it.get('choices', [])) for it in addons_plan)
    if with_modifiers: steps += sum(len(it.get('choices', [])) for it in modifiers_plan)

    # Szacowanie czasu (Total Est Seconds)
    est = 0.0
    est += _PHASE_TOTALS["categories"] * _PHASE_MAP["categories"]["est_per_item"]
    est += _PHASE_TOTALS["dishes"] * _PHASE_MAP["dishes"]["est_per_item"]
    est += _PHASE_TOTALS["sizes"] * _PHASE_MAP["sizes"]["est_per_item"]
    est += _PHASE_TOTALS["ingredients"] * _PHASE_MAP["ingredients"]["est_per_item"]

    # Złożone szacowanie dla grup
    if with_addons:
        for it in addons_plan:
            est += 5.0 + (0.5 * len(it.get('choices', [])))
    if with_modifiers:
        for it in modifiers_plan:
            est += 6.0 + (0.5 * len(it.get('choices', [])))

    return steps, est


def _dbg_highlight(driver, el, color="fuchsia"):
    try:
        driver.execute_script("arguments[0].style.outline = '3px solid ' + arguments[1];", el, color)
    except Exception:
        pass


def _count_visible(driver, css_selector: str) -> int:
    try:
        return len([e for e in driver.find_elements(By.CSS_SELECTOR, css_selector) if e.is_displayed()])
    except Exception:
        return 0


def _debug_dump_visible_addon_rows(driver, log_func):
    try:
        rows = driver.find_elements(By.XPATH,
                                    "//input[@name='entryName']/ancestor::div[contains(@class,'list-group-item')]")
        log_func(f"[Dodatki][DEBUG] Widoczne wiersze: {len(rows)}")
        for i, row in enumerate(rows, 1):
            try:
                nm = row.find_element(By.CSS_SELECTOR, "input[name='entryName']").get_attribute("value") or ""
            except Exception:
                nm = "<brak>"
            try:
                pr = row.find_element(By.CSS_SELECTOR, "input[name='price']").get_attribute("value") or ""
            except Exception:
                pr = "<brak>"
            log_func(f"[Dodatki][DEBUG] Row {i}: name='{nm}' price='{pr}'")
    except Exception as e:
        log_func(f"[Dodatki][DEBUG] dump err: {e}")


# ---- GŁÓWNA FUNKCJA UPOLOADERA ----
def upload_menu(
        driver,
        menu_json_path: str,
        skip_categories: bool = False,
        with_ingredients: bool = False,
        with_description: bool = False,
        log_func=print,
        with_sizes: bool = False,
        with_addons: bool = False,  # <— NOWE
        skip_dishes: bool = False,
        with_modifiers: bool = False,
        progress_callback=None,
        selected_groups: list = None,  # <— NOWE: lista wybranych grup
        config=None,  # <--- NOWY ARGUMENT KONFIGURACJI
):
    global _ADDONS_RAN, _MODIFIERS_RAN
    _ADDONS_RAN = False
    _MODIFIERS_RAN = False
    start_time = time.time()
    wait = WebDriverWait(driver, 20)
    from collections import OrderedDict

    if config is None:
        # Awaryjna, domyślna konfiguracja
        config = {
            'SELECTOR_TAB_BUTTON': (By.XPATH,
                                    "//button[contains(@class,'filter__btn') and .//span[contains(normalize-space(text()), '__TAB_NAME__')]]"),
            'SELECTOR_GLOBAL_SAVE_BUTTON': (By.XPATH,
                                            "//button[contains(@class,'btn-success') and (contains(.,'ZAPISZ') or contains(.,'Zapisz'))]"),
            'SELECTOR_ADD_CATEGORY_BUTTON': (By.CSS_SELECTOR, "button.btn.btn-primary.btn-sm"),
            'SELECTOR_CATEGORY_NAME_INPUT': (By.CSS_SELECTOR, "input[name='categoryName']"),
            'SELECTOR_CATEGORY_ROW': (By.XPATH,
                                      "//div[contains(@class,'list-group-item') and .//span[normalize-space(text())='__CATEGORY_NAME__']]"),
            'SELECTOR_ADD_DISH_BUTTON_IN_CAT': (By.CSS_SELECTOR, "button.btn.flex-shrink-0.ml-2.btn-primary.btn-sm"),
            'SELECTOR_BACK_BUTTON': (By.CSS_SELECTOR, "button.btn.mr-2.btn-light.btn-sm"),
            'SELECTOR_DISH_NAME_INPUT': (By.CSS_SELECTOR, "input[name='mealName'], input[name='productName']"),
            'SELECTOR_DISH_PRICE_INPUT': (By.CSS_SELECTOR, "input[name='price']"),
            'SELECTOR_DISH_DESC_INPUT': (By.CSS_SELECTOR, "textarea[name='mealDescription']"),
            'SELECTOR_DISH_SAVE_BUTTON': (By.XPATH, "//button[contains(text(),'ZAPISZ') or contains(text(),'Zapisz')]"),
            'SELECTOR_INGREDIENT_ADD_BUTTON': (By.CSS_SELECTOR, "button.addSizeButton.btn-primary.btn-sm"),
            'SELECTOR_INGREDIENT_NAME_INPUT': (By.CSS_SELECTOR, "input[name='ingredientName']"),
            'SELECTOR_INGREDIENT_SAVE_BUTTON': (By.CSS_SELECTOR, "button.btn-input.btn-success"),
            # Rozmiary (sekcja 2)
            'SELECTOR_SIZE_CATEGORY_CARD': (By.XPATH,
                                            "//div[contains(@class,'card-body')][.//span[contains(@class,'font-weight-bold') and normalize-space(text())='__CATEGORY_NAME__']]"),
            'SELECTOR_SIZE_ADD_BUTTON': (By.XPATH, ".//button[contains(., 'Dodaj rozmiar')]"),
            'SELECTOR_SIZE_NAME_INPUT': (By.CSS_SELECTOR, "input#categorySizeName[name='categorySizeName']"),
            # Rozmiary (w karcie dania)
            'SELECTOR_SIZE_ROW_IN_DISH_CARD': (By.XPATH,
                                               "//tr[contains(@class,'meal-size-list-item')][.//h4[contains(@class,'meal-size-name') and contains(normalize-space(.), '__LABEL_TEXT__')]]"),
            'SELECTOR_SIZE_PRICE_INPUT_IN_ROW': (By.XPATH, ".//input[@name='price']"),
            'SELECTOR_SIZE_ADD_TO_DISH_BUTTON': (By.XPATH, ".//button[contains(@class,'btn-success')]"),
            # Grupy (dodatki/modyfikatory)
            'SELECTOR_ADD_GROUP_BUTTON': (By.XPATH,
                                          "//button[contains(@class,'btn-primary') and contains(@class,'btn-sm') and contains(normalize-space(.), 'Dodaj grupę')]"),
            'SELECTOR_GROUP_NAME_INPUT': (By.CSS_SELECTOR, "input#choiceGroupName[name='choiceGroupName']"),
            'SELECTOR_MEAL_TREE_CONTAINER': (By.XPATH,
                                             "//h4[@id='mealsWithSelectedChoiceGroups']/ancestor::div[contains(@class,'edit-section')]"),
            'SELECTOR_GROUP_DETAILS_TAB_ADDONS': (By.XPATH,
                                                  "//a[contains(@class,'nav-link') and normalize-space(text())='Dodatki']"),
            'SELECTOR_GROUP_DETAILS_TAB_MODIFIERS': (By.XPATH,
                                                     "//a[contains(@class,'nav-link') and contains(normalize-space(text()), 'Modyfikatory')]"),
            'SELECTOR_ADD_ENTRY_BUTTON': (By.XPATH,
                                          "//button[contains(@class,'btn-primary') and contains(@class,'btn-sm') and (contains(normalize-space(.),'Dodaj modyfikator') or contains(normalize-space(.),'Dodaj dodatek') or contains(normalize-space(.),'Dodaj nowy'))]"),
            'SELECTOR_ADDON_NAME_INPUT': (By.CSS_SELECTOR, "input[name='entryName']"),
            'SELECTOR_ADDON_PRICE_INPUT': (By.CSS_SELECTOR, "input[name='price']"),
            'SELECTOR_ADDON_SAVE_ROW_BUTTON': (By.XPATH,
                                               ".//button[contains(@class,'btn-input') and contains(@class,'btn-success')]"),
            'SELECTOR_REQUIRED_TOGGLE_CONTAINER': (By.XPATH,
                                                   "//h4[contains(@class,'label') and contains(normalize-space(.),'Wymagana')]/ancestor::div[contains(@class,'edit-section')]"),
            'SELECTOR_REQUIRED_TOGGLE_CHECKBOX': (By.XPATH,
                                                  ".//label[contains(@class,'switch')]//input[@type='checkbox']"),
            'SELECTOR_REQUIRED_TOGGLE_LABEL': (By.XPATH, ".//label[contains(@class,'switch')]"),
        }

    with open(menu_json_path, 'r', encoding='utf-8') as f:
        menu = json.load(f, object_pairs_hook=OrderedDict)  # ← KOLEJNOŚĆ jak w pliku
    categories = list(menu.keys())
    total_steps, est_secs = _progress_compute_totals(
        menu,
        skip_categories=skip_categories,
        skip_dishes=skip_dishes,
        with_desc=with_description,
        with_ing=with_ingredients,
        with_sizes=with_sizes,
        with_addons=with_addons,
        with_modifiers=with_modifiers,
    )
    try:
        _progress_init(driver, total_steps, est_secs, progress_callback)
    except Exception:
        pass
    # (opcjonalnie) szybki log kontrolny, żeby widzieć kolejność:
    log_func("[Dania] Kolejność kategorii z JSON: " + " | ".join(categories))

    # 1) NAJPIERW KATEGORIE
    if not skip_categories:
        _set_phase("categories", log_func)
        for idx, cat in enumerate(categories, start=1):
            log_func(f"[{idx}/{len(categories)}] Dodaję kategorię: {cat}")
            btn = wait.until(EC.element_to_be_clickable(config['SELECTOR_ADD_CATEGORY_BUTTON']))
            btn.click()
            inp = wait.until(EC.visibility_of_element_located(config['SELECTOR_CATEGORY_NAME_INPUT']))
            inp.clear();
            inp.send_keys(cat)
            save_btn = driver.find_element(*config['SELECTOR_GLOBAL_SAVE_BUTTON'])  # użyjemy ogólnego selektora zapisu
            save_btn.click();
            time.sleep(0.5)
            _progress_tick(driver)
    else:
        log_func("Pominięto dodawanie kategorii.")

    # 2) POTEM ROZMIARY (TYLKO NAZWY), JEŚLI WŁĄCZONE
    if with_sizes:
        _set_phase("sizes", log_func)
        try:
            _create_sizes_for_categories(driver, wait, menu, categories, log_func, config)
        except Exception as e:
            log_func(f"[Rozmiary] Błąd podczas tworzenia rozmiarów: {e}")

    # 3) PRZEJDŹ DO „Dania”
    _goto_tab(wait, "Dania", config['SELECTOR_TAB_BUTTON'])

    # 4) DODAWANIE DAŃ + (opcjonalnie) CEN ROZMIARÓW W KARCIE DANIA
    if not skip_dishes:
        _set_phase("dishes", log_func)
        log_func(f"[Dania] >>> START pętli kategorii: {len(categories)} kategorii")
        for cidx, cat in enumerate(categories, start=1):
            # trzymaj kartę „Dania”
            try:
                _goto_tab(wait, "Dania", config['SELECTOR_TAB_BUTTON'])
            except Exception:
                pass

            log_func(f"[Dania][{cidx}/{len(categories)}] -> otwieram kategorię: {cat}")
            _open_category_by_name(driver, wait, cat, log_func, config)

            dishes = menu.get(cat, [])
            log_func(f"Kategoria '{cat}' - {len(dishes)} dań")

            for didx, dish in enumerate(dishes, start=1):
                name = dish.get('name', '')
                ingredients = dish.get('ingredients', [])
                opis = (dish.get('description') or '').strip()
                log_func(
                    f"[{didx}/{len(dishes)}] Dodaję danie '{name}', składników: {len(ingredients)}, opis: {'TAK' if opis else 'NIE'}")

                # „Dodaj danie”
                add_btn = wait.until(EC.element_to_be_clickable(config['SELECTOR_ADD_DISH_BUTTON_IN_CAT']))
                add_btn.click()

                variants = ((dish.get('popup_details') or {}).get('variants') or [])
                has_non_default = _has_non_default_variants(dish)

                # Nazwa
                inp = wait.until(EC.visibility_of_element_located(config['SELECTOR_DISH_NAME_INPUT']))
                inp.clear()
                inp.send_keys(name)

                # Cena bazowa / Domyślny
                if with_sizes:
                    if has_non_default:
                        log_func("   [Info] Wykryto rozmiary inne niż 'Domyślny' → pomijam cenę bazową.")
                    else:
                        base_price = _get_default_price_from_dish(dish)
                        if base_price is not None:
                            try:
                                price_inp = wait.until(
                                    EC.visibility_of_element_located(config['SELECTOR_DISH_PRICE_INPUT']))
                                price_inp.clear()
                                price_inp.send_keys(str(base_price).replace(",", "."))
                                log_func("   [Rozmiar] Brak innych rozmiarów → ustawiono cenę dla 'Domyślny'.")
                            except Exception:
                                log_func(f"   [Rozmiar] Nie można wpisać ceny domyślnej dla '{name}'.")
                        else:
                            log_func("   [Rozmiar] Brak ceny dla 'Domyślny' w JSON → pomijam.")
                else:
                    try:
                        price_inp = wait.until(EC.visibility_of_element_located(config['SELECTOR_DISH_PRICE_INPUT']))
                        price_inp.clear()
                        price_inp.send_keys(str(dish.get('price', '')).replace(' zł', '').replace(',', '.'))
                    except Exception:
                        log_func(f"Nie można wprowadzić ceny dla '{name}' (pole bazowe)")

                # ROZMIARY per danie
                if with_sizes and has_non_default:
                    try:
                        _add_sizes_to_current_dish(driver, wait, dish, log_func, config)
                    except Exception as e:
                        log_func(f"[Rozmiary] Nie udało się dodać cen rozmiarów dla '{name}': {e}")

                # Opis (opcjonalnie)
                if with_description and opis:
                    try:
                        desc_area = wait.until(EC.visibility_of_element_located(config['SELECTOR_DISH_DESC_INPUT']))
                        desc_area.clear();
                        desc_area.send_keys(opis)
                        _progress_tick(driver)
                        log_func(f"Opis wprowadzony w formularzu dla '{name}' (przed zapisem)")
                    except Exception as e:
                        log_func(f"Nie udało się wprowadzić opisu w formularzu dla '{name}': {e}")

                # ZAPISZ
                save_dish = wait.until(EC.element_to_be_clickable(config['SELECTOR_DISH_SAVE_BUTTON']))
                save_dish.click();
                time.sleep(1)
                _progress_tick(driver)

                # Błędy zapisu?
                errs = driver.find_elements(By.CSS_SELECTOR, "div.alert.alert-danger p.text-danger.small.m-0")
                if errs:
                    log_func(f"Błąd: {errs[0].text}. Ponawiam zapis.")
                    try:
                        save_dish.click();
                        time.sleep(1)
                    except:
                        pass

                # Składniki (opcjonalnie)
                if with_ingredients and ingredients:
                    _set_phase("ingredients", log_func)
                    try:
                        # Znajdź danie na liście i kliknij je
                        dish_xpath = "//div[contains(@class,'list-group-item--draggable') and .//span[normalize-space(text())='__DISH_NAME__']]"
                        dish_div = wait.until(
                            EC.element_to_be_clickable((By.XPATH, dish_xpath.replace('__DISH_NAME__', name))))
                        driver.execute_script("arguments[0].scrollIntoView(true);", dish_div)
                        dish_div.click();
                        time.sleep(1)
                    except Exception as e:
                        log_func(f"Nie można wybrać dania '{name}' do dodania składników: {e}")

                    for ing in ingredients:
                        try:
                            ing_btn = wait.until(EC.element_to_be_clickable(config['SELECTOR_INGREDIENT_ADD_BUTTON']))
                            driver.execute_script("arguments[0].scrollIntoView(true);", ing_btn)
                            ing_btn.click();
                            time.sleep(0.5)
                            inputs = driver.find_elements(*config['SELECTOR_INGREDIENT_NAME_INPUT'])
                            if not inputs:
                                log_func(f"Brak pola input dla '{ing}'");
                                continue
                            inp_ing = inputs[-1]
                            inp_ing.clear();
                            inp_ing.send_keys(ing)
                            save_ing = wait.until(EC.element_to_be_clickable(config['SELECTOR_INGREDIENT_SAVE_BUTTON']))
                            save_ing.click();
                            time.sleep(0.8)
                            _progress_tick(driver)
                        except Exception as e:
                            log_func(f"Błąd przy dodawaniu '{ing}': {e}")
                            continue

            # po kategorii: Wróć
            try:
                back_btn = driver.find_element(*config['SELECTOR_BACK_BUTTON'])
                if back_btn.is_displayed() and back_btn.is_enabled():
                    back_btn.click()
                    log_func("Kliknięto 'Wróć' po wszystkich daniach w kategorii.")
                    time.sleep(0.8)
            except Exception:
                pass

        log_func("[Dania] <<< KONIEC pętli kategorii")
    else:
        log_func("[Dania] Pominięto dodawanie dań (checkbox).")
        try:
            _goto_tab(wait, "Rozmiary", config['SELECTOR_TAB_BUTTON'])
        except Exception:
            pass

    log_func("[Dania] <<< KONIEC pętli kategorii")

    if with_addons:
        _set_phase("addons", log_func)  # upewnij się, że masz guardy fazy
        try:
            log_func("[Dodatki] Start po wszystkich kategoriach…")
            plan = _build_addons_plan_from_menu(menu, log_func, selected_groups)
            if plan:
                _apply_addons_plan(driver, wait, plan, log_func, config)
            else:
                log_func("[Dodatki] Brak grup multi_choice do utworzenia.")
        except Exception as e:
            log_func(f"[Dodatki] Błąd podczas tworzenia dodatków: {e}")

    _set_phase("done", log_func)

    if with_modifiers:
        _set_phase("modifiers", log_func)
        try:
            log_func("[Modyfikatory] Start po wszystkich kategoriach…")
            mplan = _build_modifiers_plan_from_menu(menu, log_func, selected_groups)
            if mplan:
                _apply_modifiers_plan(driver, wait, mplan, log_func, config)
            else:
                log_func("[Modyfikatory] Brak grup single_choice do utworzenia.")
        except Exception as e:
            log_func(f"[Modyfikatory] Błąd podczas tworzenia modyfikatorów: {e}")

    elapsed = time.time() - start_time
    log_func(f"Całkowity czas działania: {elapsed:.2f} sekund")
    log_func("Zakończono! Zamknij okno Chrome.")

# -----------------------------------------------
#             GUI
# -----------------------------------------------

class ModernButton(tk.Button):
    def __init__(self, master, text, command=None, bg="#3b82f6", fg="white",
                 hover_bg="#2563eb", active_bg="#1d4ed8", font=("Segoe UI", 10),
                 relief="flat", bd=0, padx=15, pady=8, **kwargs):
        super().__init__(master, text=text, command=command, bg=bg, fg=fg,
                         font=font, relief=relief, bd=bd, padx=padx, pady=pady,
                         activebackground=active_bg, activeforeground=fg, cursor="hand2", **kwargs)

        self.default_bg = bg
        self.hover_bg = hover_bg
        self.active_bg = active_bg

        self.bind("<Enter>", self.on_enter)
        self.bind("<Leave>", self.on_leave)

    def on_enter(self, event):
        if self['state'] != 'disabled':
            self.config(bg=self.hover_bg)

    def on_leave(self, event):
        if self['state'] != 'disabled':
            self.config(bg=self.default_bg)


class ModernCheckbutton(tk.Frame):
    def __init__(self, master, text, variable, accent="#3b82f6", fg="#f1f5f9", bg="#1e293b", font=("Segoe UI", 10),
                 **kwargs):
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
        # Rounded rect simulation
        if self.var.get():
            self.box.create_rectangle(1, 1, 17, 17, outline=self.accent, fill=self.accent, width=0)
            # Checkmark
            self.box.create_line(4, 9, 8, 13, width=2, fill="white", capstyle="round")
            self.box.create_line(8, 13, 14, 5, width=2, fill="white", capstyle="round")
        else:
            self.box.create_rectangle(1, 1, 17, 17, outline="#475569", fill=self.bg, width=1)

class PapuGUI:
    def __init__(self, root):
        self.root = root
        self.root.title(f"Menu Uploader {VERSION}")
        self.root.geometry("1100x800")
        self.root.minsize(950, 650)

        # --- DATA & CONFIG ---
        self.url = "https://system.papu.io/settings/menu-edit"
        self.driver = None
        self.upload_thread = None
        self.uploading = False
        self._log_lines = []
        self._last_log_path = None
        self._live_log_path = None

        # --- THEME (Dark Slate) ---
        self.config = {
            'COLOR_BG': "#0f172a",  # Main Background
            'COLOR_PANEL': "#1e293b",  # Panels/Cards
            'COLOR_FOOTER': "#020617",  # Darker Footer
            'COLOR_ACCENT': "#3b82f6",  # Blue
            'COLOR_ACCENT_HOVER': "#2563eb",
            'COLOR_SUCCESS': "#10b981",  # Green
            'COLOR_SUCCESS_HOVER': "#059669",
            'COLOR_DANGER': "#ef4444",  # Red
            'COLOR_DANGER_HOVER': "#dc2626",
            'COLOR_WARNING': "#fbbf24",
            'COLOR_TEXT_MAIN': "#f8fafc",
            'COLOR_TEXT_MUTED': "#94a3b8",
            'COLOR_BORDER': "#334155",

            'SELECTOR_TAB_BUTTON': (By.XPATH,
                                    "//button[contains(@class,'filter__btn') and .//span[contains(normalize-space(text()), '__TAB_NAME__')]]"),
            'SELECTOR_GLOBAL_SAVE_BUTTON': (By.XPATH,
                                            "//button[contains(@class,'btn-success') and (contains(.,'ZAPISZ') or contains(.,'Zapisz'))]"),
            'SELECTOR_ADD_CATEGORY_BUTTON': (By.CSS_SELECTOR, "button.btn.btn-primary.btn-sm"),
            'SELECTOR_CATEGORY_NAME_INPUT': (By.CSS_SELECTOR, "input[name='categoryName']"),
            'SELECTOR_CATEGORY_ROW': (By.XPATH,
                                      "//div[contains(@class,'list-group-item') and .//span[normalize-space(text())='__CATEGORY_NAME__']]"),
            'SELECTOR_ADD_DISH_BUTTON_IN_CAT': (By.CSS_SELECTOR, "button.btn.flex-shrink-0.ml-2.btn-primary.btn-sm"),
            'SELECTOR_BACK_BUTTON': (By.CSS_SELECTOR, "button.btn.mr-2.btn-light.btn-sm"),
            'SELECTOR_DISH_NAME_INPUT': (By.CSS_SELECTOR, "input[name='mealName'], input[name='productName']"),
            'SELECTOR_DISH_PRICE_INPUT': (By.CSS_SELECTOR, "input[name='price']"),
            'SELECTOR_DISH_DESC_INPUT': (By.CSS_SELECTOR, "textarea[name='mealDescription']"),
            'SELECTOR_DISH_SAVE_BUTTON': (By.XPATH, "//button[contains(text(),'ZAPISZ') or contains(text(),'Zapisz')]"),
            'SELECTOR_INGREDIENT_ADD_BUTTON': (By.CSS_SELECTOR, "button.addSizeButton.btn-primary.btn-sm"),
            'SELECTOR_INGREDIENT_NAME_INPUT': (By.CSS_SELECTOR, "input[name='ingredientName']"),
            'SELECTOR_INGREDIENT_SAVE_BUTTON': (By.CSS_SELECTOR, "button.btn-input.btn-success"),
            'SELECTOR_SIZE_CATEGORY_CARD': (By.XPATH,
                                            "//div[contains(@class,'card-body')][.//span[contains(@class,'font-weight-bold') and normalize-space(text())='__CATEGORY_NAME__']]"),
            'SELECTOR_SIZE_ADD_BUTTON': (By.XPATH, ".//button[contains(., 'Dodaj rozmiar')]"),
            'SELECTOR_SIZE_NAME_INPUT': (By.CSS_SELECTOR, "input#categorySizeName[name='categorySizeName']"),
            'SELECTOR_SIZE_ROW_IN_DISH_CARD': (By.XPATH,
                                               "//tr[contains(@class,'meal-size-list-item')][.//h4[contains(@class,'meal-size-name') and contains(normalize-space(.), '__LABEL_TEXT__')]]"),
            'SELECTOR_SIZE_PRICE_INPUT_IN_ROW': (By.XPATH, ".//input[@name='price']"),
            'SELECTOR_SIZE_ADD_TO_DISH_BUTTON': (By.XPATH, ".//button[contains(@class,'btn-success')]"),
            'SELECTOR_ADD_GROUP_BUTTON': (By.XPATH,
                                          "//button[contains(@class,'btn-primary') and contains(@class,'btn-sm') and contains(normalize-space(.), 'Dodaj grupę')]"),
            'SELECTOR_GROUP_NAME_INPUT': (By.CSS_SELECTOR, "input#choiceGroupName[name='choiceGroupName']"),
            'SELECTOR_MEAL_TREE_CONTAINER': (By.XPATH,
                                             "//h4[@id='mealsWithSelectedChoiceGroups']/ancestor::div[contains(@class,'edit-section')]"),
            'SELECTOR_GROUP_DETAILS_TAB_ADDONS': (By.XPATH,
                                                  "//a[contains(@class,'nav-link') and normalize-space(text())='Dodatki']"),
            'SELECTOR_GROUP_DETAILS_TAB_MODIFIERS': (By.XPATH,
                                                     "//a[contains(@class,'nav-link') and contains(normalize-space(text()), 'Modyfikatory')]"),
            'SELECTOR_ADD_ENTRY_BUTTON': (By.XPATH,
                                          "//button[contains(@class,'btn-primary') and contains(@class,'btn-sm') and (contains(normalize-space(.),'Dodaj modyfikator') or contains(normalize-space(.),'Dodaj dodatek') or contains(normalize-space(.),'Dodaj nowy'))]"),
            'SELECTOR_ADDON_NAME_INPUT': (By.CSS_SELECTOR, "input[name='entryName']"),
            'SELECTOR_ADDON_PRICE_INPUT': (By.CSS_SELECTOR, "input[name='price']"),
            'SELECTOR_ADDON_SAVE_ROW_BUTTON': (By.XPATH,
                                               ".//button[contains(@class,'btn-input') and contains(@class,'btn-success')]"),
            'SELECTOR_REQUIRED_TOGGLE_CONTAINER': (By.XPATH,
                                                   "//h4[contains(@class,'label') and contains(normalize-space(.),'Wymagana')]/ancestor::div[contains(@class,'edit-section')]"),
            'SELECTOR_REQUIRED_TOGGLE_CHECKBOX': (By.XPATH,
                                                  ".//label[contains(@class,'switch')]//input[@type='checkbox']"),
            'SELECTOR_REQUIRED_TOGGLE_LABEL': (By.XPATH, ".//label[contains(@class,'switch')]"),
        }

        # --- VARIABLES ---
        self.skip_categories_var = tk.BooleanVar()
        self.with_ingredients_var = tk.BooleanVar()
        self.with_description_var = tk.BooleanVar()
        self.with_sizes_var = tk.BooleanVar()
        self.with_addons_var = tk.BooleanVar()
        self.with_modifiers_var = tk.BooleanVar()
        self.skip_dishes_var = tk.BooleanVar(value=False)

        self.addon_vars = {}
        self.addon_checkboxes = {}
        self.modifier_vars = {}
        self.modifier_checkboxes = {}

        # --- LAYOUT BUILD ---
        self.root.configure(bg=self.config['COLOR_BG'])

        # 1. FOOTER (Przypięty na dole)
        self._build_sticky_footer()

        # 2. MAIN CONTAINER (Reszta okna nad stopką)
        self.main_container = tk.Frame(self.root, bg=self.config['COLOR_BG'])
        self.main_container.pack(side="top", fill="both", expand=True, padx=20, pady=10)

        # Header & File
        self._build_header(self.main_container)
        self._build_file_section(self.main_container)

        # 3. MIDDLE SPLIT SECTION (Opcje + Grupy obok siebie)
        self.middle_frame = tk.Frame(self.main_container, bg=self.config['COLOR_BG'])
        self.middle_frame.pack(fill="x", pady=10)
        self.middle_frame.grid_columnconfigure(0, weight=1)  # Left col (Options)
        self.middle_frame.grid_columnconfigure(1, weight=2)  # Right col (Groups) - szersza

        self._build_options_panel(self.middle_frame)
        self._build_groups_panel(self.middle_frame)

        # 4. LOGS (Zajmują resztę miejsca)
        self._build_logs_panel(self.main_container)

        self.gui_minimized = False
        self._init_live_log()

    def load_settings(self):
        """Ładuje email/hasło z pliku settings.json"""
        try:
            if os.path.exists("settings.json"):
                with open("settings.json", "r", encoding="utf-8") as f:
                    data = json.load(f)
                    return data.get("email", ""), data.get("password", "")
        except Exception:
            pass
        return "", ""

    def _perform_auto_login(self, driver):
        """Automatyczne logowanie (Dane z pliku settings.json)"""
        email, password = self.load_settings()  # Pobieramy z pliku

        if not email or not password:
            self.log_print("Brak zapisanych danych logowania - pomijam auto-login.", "warning")
            return

        self.log_print("Próba automatycznego logowania...", "info")
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

            self.log_print("Dane logowania wysłane.", "success")

        except Exception as e:
            self.log_print(f"Nie udało się zalogować automatycznie: {e}", "error")

    def open_settings_window(self):
        """Otwiera popup z ustawieniami logowania"""
        top = tk.Toplevel(self.root)
        top.title("Ustawienia Logowania")
        top.geometry("400x320")
        top.configure(bg=self.config['COLOR_PANEL'])
        top.resizable(False, False)

        # ... (POZYCJONOWANIE I UI BEZ ZMIAN - SKOPIUJ ZE STAREGO KODU) ...
        # (Skopiuj środek funkcji z poprzedniej odpowiedzi, tutaj pokazuję tylko zmienioną funkcję save_and_close)

        # Centrowanie
        x = self.root.winfo_x() + (self.root.winfo_width() // 2) - 200
        y = self.root.winfo_y() + (self.root.winfo_height() // 2) - 160
        top.geometry(f"+{x}+{y}")

        tk.Label(top, text="🔐 Dane do Auto-Logowania", font=("Segoe UI", 12, "bold"), bg=self.config['COLOR_PANEL'],
                 fg="white").pack(pady=(20, 5))
        tk.Label(top, text="Zapisz email i hasło do systemu Papu.io", font=("Segoe UI", 9),
                 bg=self.config['COLOR_PANEL'], fg=self.config['COLOR_TEXT_MUTED']).pack(pady=(0, 20))

        form = tk.Frame(top, bg=self.config['COLOR_PANEL'], padx=30)
        form.pack(fill="x")

        saved_email, saved_pass = self.load_settings()

        tk.Label(form, text="Email:", bg=self.config['COLOR_PANEL'], fg="#cbd5e1", font=("Segoe UI", 9)).pack(
            anchor="w")
        email_entry = tk.Entry(form, font=("Segoe UI", 10), bg="#0f172a", fg="white", relief="flat", bd=1,
                               highlightthickness=1, highlightbackground=self.config['COLOR_BORDER'])
        email_entry.pack(fill="x", pady=(2, 10), ipady=4)
        email_entry.insert(0, saved_email)

        tk.Label(form, text="Hasło:", bg=self.config['COLOR_PANEL'], fg="#cbd5e1", font=("Segoe UI", 9)).pack(
            anchor="w")
        pass_entry = tk.Entry(form, font=("Segoe UI", 10), bg="#0f172a", fg="white", relief="flat", bd=1,
                              highlightthickness=1, highlightbackground=self.config['COLOR_BORDER'], show="•")
        pass_entry.pack(fill="x", pady=(2, 20), ipady=4)
        pass_entry.insert(0, saved_pass)

        # --- ZMODYFIKOWANA FUNKCJA ZAPISU ---
        def save_and_close():
            data = {
                "email": email_entry.get().strip(),
                "password": pass_entry.get().strip()
            }
            try:
                with open("settings.json", "w", encoding="utf-8") as f:
                    json.dump(data, f)
                self.log_print("Zaktualizowano dane logowania.", "success")

                # NATYCHMIASTOWY RESET PRZYCISKU (UX)
                self.account_btn.config(bg=self.config['COLOR_PANEL'], fg="white")
                self.account_btn.default_bg = self.config['COLOR_PANEL']

                top.destroy()
            except Exception as e:
                messagebox.showerror("Błąd", f"Nie udało się zapisać: {e}")

        # ------------------------------------

        btns = tk.Frame(top, bg=self.config['COLOR_PANEL'])
        btns.pack(pady=10)
        ModernButton(btns, text="Anuluj", command=top.destroy, bg=self.config['COLOR_BORDER'], hover_bg="#475569",
                     padx=15).pack(side="left", padx=5)
        ModernButton(btns, text="💾 Zapisz", command=save_and_close, bg=self.config['COLOR_SUCCESS'],
                     hover_bg=self.config['COLOR_SUCCESS_HOVER'], padx=15).pack(side="left", padx=5)

    def _build_sticky_footer(self):
        """Tworzy panel dolny, który ZAWSZE jest widoczny."""
        self.footer_frame = tk.Frame(self.root, bg=self.config['COLOR_FOOTER'], height=80)
        self.footer_frame.pack(side="bottom", fill="x")

        # Container with padding inside footer
        footer_content = tk.Frame(self.footer_frame, bg=self.config['COLOR_FOOTER'], padx=20, pady=15)
        footer_content.pack(fill="both", expand=True)

        # Progress Section (Left side of footer)
        self.progress_wrapper = tk.Frame(footer_content, bg=self.config['COLOR_FOOTER'])
        self.progress_wrapper.pack(side="left", fill="x", expand=True, padx=(0, 20))

        # POPRAWKA: mb=5 -> pady=(0, 5)
        self.progress_info = tk.Frame(self.progress_wrapper, bg=self.config['COLOR_FOOTER'])
        self.progress_info.pack(fill="x", pady=(0, 5))

        self.eta_label = tk.Label(self.progress_info, text="--:--", bg=self.config['COLOR_FOOTER'],
                                  fg=self.config['COLOR_ACCENT'], font=("Segoe UI", 9, "bold"))
        self.eta_label.pack(side="left")
        self.progress_status = tk.Label(self.progress_info, text="Gotowy", bg=self.config['COLOR_FOOTER'],
                                        fg=self.config['COLOR_TEXT_MUTED'], font=("Segoe UI", 9))
        self.progress_status.pack(side="right")

        style = ttk.Style()
        style.configure("Modern.Horizontal.TProgressbar", background=self.config['COLOR_ACCENT'],
                        troughcolor=self.config['COLOR_BORDER'], thickness=8)
        self.progress_bar = ttk.Progressbar(self.progress_wrapper, style="Modern.Horizontal.TProgressbar",
                                            mode='determinate')
        self.progress_bar.pack(fill="x")

        # Buttons Section (Right side of footer)
        self.buttons_wrapper = tk.Frame(footer_content, bg=self.config['COLOR_FOOTER'])
        self.buttons_wrapper.pack(side="right")

        self.open_chrome_button = ModernButton(self.buttons_wrapper, text="🌐 Otwórz Chrome", command=self.open_chrome,
                                               bg=self.config['COLOR_BORDER'], hover_bg="#475569",
                                               font=("Segoe UI", 10, "bold"))
        self.open_chrome_button.pack(side="left", padx=5)

        self.start_button = ModernButton(self.buttons_wrapper, text="🚀 START", command=self.start_upload,
                                         bg=self.config['COLOR_SUCCESS'], hover_bg=self.config['COLOR_SUCCESS_HOVER'],
                                         font=("Segoe UI", 10, "bold"), padx=25)
        self.start_button.pack(side="left", padx=5)
        self.start_button.pack_forget()  # Ukryty na start

        self.stop_button = ModernButton(self.buttons_wrapper, text="⏹ STOP", command=self.stop_upload,
                                        bg=self.config['COLOR_DANGER'], hover_bg=self.config['COLOR_DANGER_HOVER'],
                                        font=("Segoe UI", 10, "bold"), padx=20)
        self.stop_button.pack(side="left", padx=5)
        self.stop_button.pack_forget()  # Ukryty na start

    def _build_header(self, parent):
        header = tk.Frame(parent, bg=self.config['COLOR_BG'])
        header.pack(fill="x", pady=(0, 15))

        # Left side
        left = tk.Frame(header, bg=self.config['COLOR_BG'])
        left.pack(side="left")
        tk.Label(left, text="🍽️ Menu Uploader", font=("Segoe UI", 20, "bold"),
                 fg=self.config['COLOR_TEXT_MAIN'], bg=self.config['COLOR_BG']).pack(side="left")
        tk.Label(left, text=f"v{VERSION}", font=("Segoe UI", 10),
                 fg=self.config['COLOR_TEXT_MUTED'], bg=self.config['COLOR_BG']).pack(side="left", padx=10,
                                                                                      pady=(10, 0))

        # Right side
        right = tk.Frame(header, bg=self.config['COLOR_BG'])
        right.pack(side="right")

        # MODIFICATION: Assign to self.account_btn and start blinking check
        self.account_btn = ModernButton(right, text="🔐 Konto", command=self.open_settings_window,
                                        bg=self.config['COLOR_PANEL'], hover_bg="#334155",
                                        font=("Segoe UI", 9, "bold"), padx=15, pady=6)
        self.account_btn.pack()

        # Start blinking check immediately
        self._blink_account_btn()

    def _build_options_panel(self, parent_grid):
        """Panel Opcji - Lewa kolumna"""
        self.options_frame = tk.Frame(parent_grid, bg=self.config['COLOR_PANEL'], padx=15, pady=15)
        self.options_frame.grid(row=0, column=0, sticky="nsew", padx=(0, 10))

        # POPRAWKA: mb=10 -> pady=(0, 10)
        tk.Label(self.options_frame, text="⚙️ Konfiguracja", font=("Segoe UI", 10, "bold"),
                 fg=self.config['COLOR_TEXT_MAIN'], bg=self.config['COLOR_PANEL']).pack(anchor="w", pady=(0, 10))

        # Checkboxy jeden pod drugim
        ModernCheckbutton(self.options_frame, "Pomiń kategorie", self.skip_categories_var,
                          accent=self.config['COLOR_ACCENT'], bg=self.config['COLOR_PANEL']).pack(anchor="w", pady=2)
        ModernCheckbutton(self.options_frame, "Pomiń dania", self.skip_dishes_var, accent=self.config['COLOR_ACCENT'],
                          bg=self.config['COLOR_PANEL']).pack(anchor="w", pady=2)
        ModernCheckbutton(self.options_frame, "Opisy dań", self.with_description_var,
                          accent=self.config['COLOR_ACCENT'], bg=self.config['COLOR_PANEL']).pack(anchor="w", pady=2)
        tk.Frame(self.options_frame, height=1, bg=self.config['COLOR_BORDER']).pack(fill="x", pady=8)
        ModernCheckbutton(self.options_frame, "Rozmiary", self.with_sizes_var, accent=self.config['COLOR_ACCENT'],
                          bg=self.config['COLOR_PANEL']).pack(anchor="w", pady=2)
        ModernCheckbutton(self.options_frame, "Składniki", self.with_ingredients_var,
                          accent=self.config['COLOR_ACCENT'], bg=self.config['COLOR_PANEL']).pack(anchor="w", pady=2)
        ModernCheckbutton(self.options_frame, "Dodatki (Multi)", self.with_addons_var,
                          accent=self.config['COLOR_ACCENT'], bg=self.config['COLOR_PANEL']).pack(anchor="w", pady=2)
        ModernCheckbutton(self.options_frame, "Modyfikatory (Single)", self.with_modifiers_var,
                          accent=self.config['COLOR_ACCENT'], bg=self.config['COLOR_PANEL']).pack(anchor="w", pady=2)

    def _build_groups_panel(self, parent_grid):
        """Panel Grup - Prawa kolumna (Widoczny tylko gdy są grupy)"""
        self.groups_frame = tk.Frame(parent_grid, bg=self.config['COLOR_PANEL'], padx=2, pady=2)
        self.groups_frame.grid(row=0, column=1, sticky="nsew")
        self.groups_frame.grid_remove()  # Domyślnie ukryty

        container = tk.Frame(self.groups_frame, bg=self.config['COLOR_PANEL'], padx=10, pady=10)
        container.pack(fill="both", expand=True)

        # Header with buttons
        # POPRAWKA: mb=5 -> pady=(0, 5)
        head = tk.Frame(container, bg=self.config['COLOR_PANEL'])
        head.pack(fill="x", pady=(0, 5))
        tk.Label(head, text="🎯 Wybór Grup", font=("Segoe UI", 10, "bold"), fg=self.config['COLOR_TEXT_MAIN'],
                 bg=self.config['COLOR_PANEL']).pack(side="left")

        btns = tk.Frame(head, bg=self.config['COLOR_PANEL'])
        btns.pack(side="right")
        ModernButton(btns, text="Wszystkie", command=self.select_all_groups, bg=self.config['COLOR_BORDER'],
                     font=("Segoe UI", 8), padx=8, pady=2).pack(side="left", padx=2)
        ModernButton(btns, text="Żadne", command=self.deselect_all_groups, bg=self.config['COLOR_BORDER'],
                     font=("Segoe UI", 8), padx=8, pady=2).pack(side="left")

        # Notebook
        style = ttk.Style()
        style.theme_use('clam')
        style.configure('TNotebook', background=self.config['COLOR_PANEL'], borderwidth=0)
        style.configure('TNotebook.Tab', background=self.config['COLOR_BORDER'],
                        foreground=self.config['COLOR_TEXT_MAIN'], padding=[10, 5], borderwidth=0)
        style.map('TNotebook.Tab', background=[('selected', self.config['COLOR_ACCENT'])])

        self.groups_notebook = ttk.Notebook(container)
        self.groups_notebook.pack(fill="both", expand=True)

        self.addons_tab = tk.Frame(self.groups_notebook, bg=self.config['COLOR_PANEL'])
        self.groups_notebook.add(self.addons_tab, text="🍕 Dodatki")

        self.modifiers_tab = tk.Frame(self.groups_notebook, bg=self.config['COLOR_PANEL'])
        self.groups_notebook.add(self.modifiers_tab, text="⚙️ Modyfikatory")

        self._create_scrollable_tab(self.addons_tab, 'addons')
        self._create_scrollable_tab(self.modifiers_tab, 'modifiers')

    def _build_logs_panel(self, parent):
        log_frame = tk.Frame(parent, bg=self.config['COLOR_BG'])
        log_frame.pack(fill="both", expand=True, pady=(10, 0))

        # POPRAWKA: mb=2 -> pady=(0, 2)
        tk.Label(log_frame, text="📋 Logi Operacji", font=("Segoe UI", 9, "bold"), fg=self.config['COLOR_TEXT_MUTED'],
                 bg=self.config['COLOR_BG']).pack(anchor="w", pady=(0, 2))

        txt_cont = tk.Frame(log_frame, bg="#020617", bd=1, relief="solid")
        txt_cont.pack(fill="both", expand=True)

        self.log = tk.Text(txt_cont, state="disabled", font=("Consolas", 9), bg="#020617", fg="#cbd5e1", relief="flat",
                           padx=10, pady=10)
        self.log.pack(side="left", fill="both", expand=True)

        sb = tk.Scrollbar(txt_cont, command=self.log.yview, bg=self.config['COLOR_BG'])
        sb.pack(side="right", fill="y")
        self.log.config(yscrollcommand=sb.set)

        # Tagi kolorów
        self.log.tag_config("color_success", foreground=self.config['COLOR_SUCCESS'])
        self.log.tag_config("color_error", foreground=self.config['COLOR_DANGER'])
        self.log.tag_config("color_warning", foreground="#fbbf24")
        self.log.tag_config("color_info", foreground=self.config['COLOR_TEXT_MUTED'])

    def _build_file_section(self, parent):
        card = tk.Frame(parent, bg=self.config['COLOR_PANEL'], padx=15, pady=15)
        card.pack(fill="x", pady=(0, 10))

        tk.Label(card, text="📁 Plik JSON", font=("Segoe UI", 10, "bold"), fg=self.config['COLOR_TEXT_MAIN'],
                 bg=self.config['COLOR_PANEL']).pack(anchor="w", pady=(0, 5))

        row = tk.Frame(card, bg=self.config['COLOR_PANEL'])
        row.pack(fill="x")

        self.menu_entry = tk.Entry(row, font=("Consolas", 10), bg="#0f172a", fg="white", insertbackground="white",
                                   relief="flat", bd=1, highlightthickness=1,
                                   highlightbackground=self.config['COLOR_BORDER'])
        self.menu_entry.pack(side="left", fill="x", expand=True, ipady=5, padx=(0, 10))

        # POPRAWKA: Przypisanie do self.menu_button
        self.menu_button = ModernButton(row, text="Wybierz", command=self.choose_menu, bg=self.config['COLOR_ACCENT'],
                                        font=("Segoe UI", 9, "bold"))
        self.menu_button.pack(side="left")

        # POPRAWKA: Przypisanie do self.preview_button
        self.preview_button = ModernButton(row, text="Podgląd", command=self.preview_json,
                                           bg=self.config['COLOR_BORDER'], font=("Segoe UI", 9), padx=10)
        self.preview_button.pack(side="left", padx=(5, 0))

        self.json_status_label = tk.Label(card, text="", bg=self.config['COLOR_PANEL'], font=("Segoe UI", 9))
        self.json_status_label.pack(anchor="w", pady=(5, 0))

    def _build_options_section(self):
        """Builds the configuration options card."""
        self.options_frame = tk.Frame(self.root, bg=self.config['COLOR_CARD'], padx=2, pady=2)
        self.options_frame.grid(row=2, column=0, sticky="ew", padx=20, pady=10)

        container = tk.Frame(self.options_frame, bg=self.config['COLOR_CARD'], padx=15, pady=15)
        container.pack(fill="both", expand=True)

        # Label (Poprawiono mb=10 na pady=(0, 10))
        tk.Label(container, text="⚙️ Konfiguracja", font=("Segoe UI", 10, "bold"),
                 fg=self.config['COLOR_TEXT_MAIN'], bg=self.config['COLOR_CARD']).pack(anchor="w", pady=(0, 10))

        # Grid for checkboxes (2 columns)
        grid_frame = tk.Frame(container, bg=self.config['COLOR_CARD'])
        grid_frame.pack(fill="x")
        grid_frame.grid_columnconfigure(0, weight=1)
        grid_frame.grid_columnconfigure(1, weight=1)

        # Column 1: Basic
        col1 = tk.Frame(grid_frame, bg=self.config['COLOR_CARD'])
        col1.grid(row=0, column=0, sticky="nw")

        ModernCheckbutton(col1, "Pomiń kategorie", self.skip_categories_var, accent=self.config['COLOR_ACCENT'],
                          bg=self.config['COLOR_CARD']).pack(anchor="w", pady=2)
        ModernCheckbutton(col1, "Pomiń dania", self.skip_dishes_var, accent=self.config['COLOR_ACCENT'],
                          bg=self.config['COLOR_CARD']).pack(anchor="w", pady=2)
        ModernCheckbutton(col1, "Dodaj opisy dań", self.with_description_var, accent=self.config['COLOR_ACCENT'],
                          bg=self.config['COLOR_CARD']).pack(anchor="w", pady=2)

        # Column 2: Advanced
        col2 = tk.Frame(grid_frame, bg=self.config['COLOR_CARD'])
        col2.grid(row=0, column=1, sticky="nw")

        ModernCheckbutton(col2, "Dodaj rozmiary", self.with_sizes_var, accent=self.config['COLOR_ACCENT'],
                          bg=self.config['COLOR_CARD']).pack(anchor="w", pady=2)
        ModernCheckbutton(col2, "Dodaj składniki", self.with_ingredients_var, accent=self.config['COLOR_ACCENT'],
                          bg=self.config['COLOR_CARD']).pack(anchor="w", pady=2)
        ModernCheckbutton(col2, "Dodaj dodatki (Grupy Multi)", self.with_addons_var, accent=self.config['COLOR_ACCENT'],
                          bg=self.config['COLOR_CARD']).pack(anchor="w", pady=2)
        ModernCheckbutton(col2, "Dodaj modyfikatory (Grupy Single)", self.with_modifiers_var,
                          accent=self.config['COLOR_ACCENT'], bg=self.config['COLOR_CARD']).pack(anchor="w", pady=2)

    def _build_groups_section(self):
        """Builds the container for dynamic group selection (hidden by default)."""
        self.groups_frame = tk.Frame(self.root, bg=self.config['COLOR_CARD'])
        self.groups_frame.grid(row=3, column=0, sticky="ew", padx=20, pady=5)
        self.groups_frame.grid_remove()  # Hidden initially

        container = tk.Frame(self.groups_frame, bg=self.config['COLOR_CARD'], padx=15, pady=10)
        container.pack(fill="both", expand=True)

        # Header (Poprawiono mb=5 na pady=(0, 5))
        header = tk.Frame(container, bg=self.config['COLOR_CARD'])
        header.pack(fill="x", pady=(0, 5))

        tk.Label(header, text="🎯 Wybierz Grupy", font=("Segoe UI", 10, "bold"),
                 fg=self.config['COLOR_TEXT_MAIN'], bg=self.config['COLOR_CARD']).pack(side="left")

        # Selection controls
        btn_frame = tk.Frame(header, bg=self.config['COLOR_CARD'])
        btn_frame.pack(side="right")

        ModernButton(btn_frame, text="Wszystkie", command=self.select_all_groups,
                     bg=self.config['COLOR_BORDER'], hover_bg="#475569", font=("Segoe UI", 8), padx=8, pady=2).pack(
            side="left", padx=2)
        ModernButton(btn_frame, text="Żadne", command=self.deselect_all_groups,
                     bg=self.config['COLOR_BORDER'], hover_bg="#475569", font=("Segoe UI", 8), padx=8, pady=2).pack(
            side="left", padx=2)

        # Notebook setup
        style = ttk.Style()
        style.theme_use('clam')
        style.configure('TNotebook', background=self.config['COLOR_CARD'], borderwidth=0)
        style.configure('TNotebook.Tab', background=self.config['COLOR_BORDER'],
                        foreground=self.config['COLOR_TEXT_MAIN'], padding=[10, 5], borderwidth=0)
        style.map('TNotebook.Tab', background=[('selected', self.config['COLOR_ACCENT'])])

        self.groups_notebook = ttk.Notebook(container)
        self.groups_notebook.pack(fill="both", expand=True)

        self.addons_tab = tk.Frame(self.groups_notebook, bg=self.config['COLOR_CARD'])
        self.groups_notebook.add(self.addons_tab, text="🍕 Dodatki")

        self.modifiers_tab = tk.Frame(self.groups_notebook, bg=self.config['COLOR_CARD'])
        self.groups_notebook.add(self.modifiers_tab, text="⚙️ Modyfikatory")

        self._create_scrollable_tab(self.addons_tab, 'addons')
        self._create_scrollable_tab(self.modifiers_tab, 'modifiers')

    def _build_logs_section(self):
        """Builds the resizable log section."""
        log_container = tk.Frame(self.root, bg=self.config['COLOR_BG'])
        log_container.grid(row=4, column=0, sticky="nsew", padx=20, pady=(10, 5))

        # Label (Poprawiono mb=2 na pady=(0, 2))
        tk.Label(log_container, text="📋 Logi Systemowe", font=("Segoe UI", 9, "bold"),
                 fg=self.config['COLOR_TEXT_MUTED'], bg=self.config['COLOR_BG']).pack(anchor="w", pady=(0, 2))

        # Text Area with Scrollbar
        text_frame = tk.Frame(log_container, bg=self.config['COLOR_BG'], bd=1, relief="solid")
        text_frame.pack(fill="both", expand=True)

        self.log = tk.Text(text_frame, state="disabled", font=("Consolas", 9),
                           bg="#020617", fg="#cbd5e1", insertbackground="white",
                           relief="flat", padx=10, pady=10)
        self.log.pack(side="left", fill="both", expand=True)

        scrollbar = tk.Scrollbar(text_frame, orient="vertical", command=self.log.yview, bg=self.config['COLOR_BG'])
        scrollbar.pack(side="right", fill="y")
        self.log.config(yscrollcommand=scrollbar.set)

        # Tags for coloring logs
        self.log.tag_config("color_error", foreground="#f87171")
        self.log.tag_config("color_success", foreground="#34d399")
        self.log.tag_config("color_warning", foreground="#fbbf24")
        self.log.tag_config("color_info", foreground="#94a3b8")

    def _build_progress_section(self):
        """Builds the progress bar section."""
        self.progress_frame = tk.Frame(self.root, bg=self.config['COLOR_BG'])
        self.progress_frame.grid(row=5, column=0, sticky="ew", padx=20, pady=5)
        self.progress_frame.grid_remove()

        # Poprawiono mb=2 na pady=(0, 2)
        info_row = tk.Frame(self.progress_frame, bg=self.config['COLOR_BG'])
        info_row.pack(fill="x", pady=(0, 2))

        self.eta_label = tk.Label(info_row, text="ETA: --:--", bg=self.config['COLOR_BG'],
                                  fg=self.config['COLOR_ACCENT'], font=("Segoe UI", 9, "bold"))
        self.eta_label.pack(side="left")

        self.progress_status = tk.Label(info_row, text="Inicjalizacja...", bg=self.config['COLOR_BG'],
                                        fg=self.config['COLOR_TEXT_MAIN'], font=("Segoe UI", 9))
        self.progress_status.pack(side="right")

        style = ttk.Style()
        style.configure("Horizontal.TProgressbar", background=self.config['COLOR_ACCENT'],
                        troughcolor=self.config['COLOR_BORDER'], thickness=6)

        self.progress_bar = ttk.Progressbar(self.progress_frame, style="Horizontal.TProgressbar", mode='determinate')
        self.progress_bar.pack(fill="x")

    def _build_action_section(self):
        """Builds the bottom action buttons."""
        self.action_frame = tk.Frame(self.root, bg=self.config['COLOR_BG'])
        self.action_frame.grid(row=6, column=0, sticky="ew", padx=20, pady=20)

        self.action_frame.grid_columnconfigure(0, weight=1)
        self.action_frame.grid_columnconfigure(1, weight=1)

        self.open_chrome_button = ModernButton(self.action_frame, text="🌐 Otwórz Chrome", command=self.open_chrome,
                                               bg=self.config['COLOR_BORDER'], hover_bg="#475569",
                                               font=("Segoe UI", 11, "bold"), pady=12)
        self.open_chrome_button.grid(row=0, column=0, padx=(0, 10), sticky="ew")

        self.start_button = ModernButton(self.action_frame, text="🚀 Rozpocznij Upload", command=self.start_upload,
                                         bg=self.config['COLOR_SUCCESS'], hover_bg=self.config['COLOR_SUCCESS_HOVER'],
                                         font=("Segoe UI", 11, "bold"), pady=12)
        self.start_button.grid(row=0, column=1, padx=(10, 0), sticky="ew")
        self.start_button.grid_remove()

        self.stop_button = ModernButton(self.action_frame, text="⏹ ZATRZYMAJ", command=self.stop_upload,
                                        bg=self.config['COLOR_DANGER'], hover_bg=self.config['COLOR_DANGER_HOVER'],
                                        font=("Segoe UI", 11, "bold"), pady=12)
        self.stop_button.grid(row=0, column=1, padx=(10, 0), sticky="ew")
        self.stop_button.grid_remove()

    def _blink_account_btn(self):
        """Makes the account button blink if no credentials are saved."""
        try:
            email, password = self.load_settings()

            # If credentials exist, ensure normal style and stop blinking
            if email and password:
                self.account_btn.config(bg=self.config['COLOR_PANEL'], fg="white")
                self.account_btn.default_bg = self.config['COLOR_PANEL']  # Reset hover base
                return

            # If missing, toggle color
            current_bg = self.account_btn.cget("bg")
            # Blink color (Amber/Warning) vs Normal Panel Color
            blink_color = "#d97706"  # Amber-600
            normal_color = self.config['COLOR_PANEL']

            new_bg = blink_color if current_bg == normal_color else normal_color
            new_fg = "white"  # Keep text white for readability

            self.account_btn.config(bg=new_bg, fg=new_fg)
            self.account_btn.default_bg = new_bg  # Update for hover effect logic

            # Schedule next check/blink in 800ms
            self.root.after(800, self._blink_account_btn)

        except Exception:
            pass  # Handle window close

    # NOWA METODA DLA PRZYCISKU KOPIOWANIA
    def copy_json_template(self):
        """Kopiuje szablon JSON do schowka."""
        json_template = """{
  "Nazwa Pierwszej Kategorii (np. Pizza)": [
    {
      "name": "Nazwa Dania A (np. Klasyczna Margherita)",
      "price": 29.99,
      "description": "To jest pole na opis dania (opcjonalne).",
      "ingredients": [
        "lista",
        "skladnikow",
        "w formie listy (opcjonalne)"
      ]
    },
    {
      "name": "Nazwa Dania B",
      "price": 45.00
    }
  ],
  "Nazwa Drugiej Kategorii (np. Napoje)": [
    {
      "name": "Nazwa Dania C",
      "price": 6.00
    }
  ]
}"""
        try:
            self.root.clipboard_clear()
            self.root.clipboard_append(json_template)
            self.log_print("📋 Szablon JSON został skopiowany do schowka.", "success")
        except Exception as e:
            self.log_print(f"❌ Błąd kopiowania do schowka: {e}", "error")

    # ... (pozostałe metody klasy PapuGUI - bez zmian) ...
    def _init_live_log(self):
        """Inicjalizuje plik logu na żywo"""
        try:
            log_dir = os.path.join(os.getcwd(), "logs")
            os.makedirs(log_dir, exist_ok=True)
            timestamp = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
            self._live_log_path = os.path.join(log_dir, f"papu_live_session_{timestamp}.log")

            with open(self._live_log_path, 'w', encoding='utf-8') as f:
                f.write(f"Papu Menu Uploader {VERSION} - Live Session Log\n")
                f.write(f"Started: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
                f.write(f"URL: {self.url}\n")
                f.write("-" * 60 + "\n")

        except Exception as e:
            print(f"Błąd inicjalizacji live logu: {e}")
            self._live_log_path = None

    def _write_to_live_log(self, message, msg_type="info"):
        """Zapisuje wiadomość do pliku logu w czasie rzeczywistym"""
        if not hasattr(self, '_live_log_path') or not self._live_log_path:
            return

        try:
            timestamp = datetime.now().strftime("%H:%M:%S")

            icons = {
                "info": "ℹ️",
                "success": "✅",
                "error": "❌",
                "warning": "⚠️"
            }

            icon = icons.get(msg_type, "ℹ️")
            log_line = f"[{timestamp}] {icon} {message}\n"

            with open(self._live_log_path, 'a', encoding='utf-8') as f:
                f.write(log_line)

        except Exception as e:
            print(f"Błąd zapisu do live logu: {e}")

    def _create_scrollable_tab(self, parent, tab_type):
        """Tworzy scrollowalną zakładkę dla grup (Fix: COLOR_PANEL)"""
        # Używamy COLOR_PANEL zamiast COLOR_CARD
        canvas = tk.Canvas(parent, bg=self.config['COLOR_PANEL'], height=200, highlightthickness=0)

        scrollbar = tk.Scrollbar(parent, orient="vertical", command=canvas.yview,
                                 bg=self.config['COLOR_BG'], troughcolor=self.config['COLOR_PANEL'],
                                 activebackground=self.config['COLOR_ACCENT'],
                                 highlightthickness=0, bd=0)

        scrollable_frame = tk.Frame(canvas, bg=self.config['COLOR_PANEL'])

        scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )

        canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)

        canvas.pack(side="left", fill="both", expand=True, padx=(10, 0), pady=10)
        scrollbar.pack(side="right", fill="y", pady=10)

        if tab_type == 'addons':
            self.addons_canvas = canvas
            self.addons_scrollbar = scrollbar
            self.addons_scrollable_frame = scrollable_frame
        else:
            self.modifiers_canvas = canvas
            self.modifiers_scrollbar = scrollbar
            self.modifiers_scrollable_frame = scrollable_frame

    def scan_menu_groups(self, menu_path):
        """Skanuje plik JSON w poszukiwaniu unikalnych grup dodatków i modyfikatorów z hashami"""
        try:
            with open(menu_path, 'r', encoding='utf-8') as f:
                menu_data = json.load(f)

            unique_addons = OrderedDict()
            unique_modifiers = OrderedDict()

            for category_name, dishes in menu_data.items():
                for dish in dishes:
                    dish_name = _norm_text(dish.get('name', ''))
                    if 'popup_details' in dish and 'variants' in dish['popup_details']:
                        for variant in dish['popup_details']['variants']:
                            if 'groups' in variant:
                                size_label = _canon_size_label(variant.get('label', ''))

                                for group in variant['groups']:
                                    group_name = _norm_text(group.get('group_name', ''))
                                    if not group_name:
                                        continue

                                    group_type = group.get('group', '')
                                    type_field = group.get('type', '')
                                    required = bool(group.get('required', False))

                                    choices = []
                                    for ch in (group.get('choices') or []):
                                        nm = _norm_text(ch.get('name') or "")
                                        if nm:
                                            pr = ch.get('price', None)
                                            if pr is None:
                                                pr = _price_to_float(ch.get('price_text') or "")
                                            choices.append({'name': nm, 'price': pr})

                                    if not choices:
                                        continue

                                    group_item = {
                                        'group_name': group_name,
                                        'size_label': size_label,
                                        'required': required,
                                        'choices': choices,
                                        'targets': {category_name: {size_label: {dish_name}}}
                                    }

                                    is_addon = (group_type == 'multi_choice_group' or type_field == 'multi')
                                    is_modifier = (group_type in ['single_choice_group',
                                                                  'single_choice_grup'] or type_field == 'single')

                                    if is_addon:
                                        unique_title = _unique_group_title(group_item, 'add')
                                        if unique_title not in unique_addons:
                                            unique_addons[unique_title] = {
                                                'title': unique_title,
                                                'base_name': group_name,
                                                'size_label': size_label
                                            }
                                    elif is_modifier:
                                        unique_title = _unique_group_title(group_item, 'mod')
                                        if unique_title not in unique_modifiers:
                                            unique_modifiers[unique_title] = {
                                                'title': unique_title,
                                                'base_name': group_name,
                                                'size_label': size_label
                                            }

            return {
                'addons': list(unique_addons.keys()),
                'modifiers': list(unique_modifiers.keys())
            }
        except Exception as e:
            self.log_print(f"Błąd skanowania grup: {e}", "error")
            return {'addons': [], 'modifiers': []}

    def populate_groups_checkboxes(self, groups_data):
        """Wypełnia zakładki checkboxami dla znalezionych grup"""
        for widget in self.addons_scrollable_frame.winfo_children():
            widget.destroy()
        for widget in self.modifiers_scrollable_frame.winfo_children():
            widget.destroy()

        self.addon_vars.clear()
        self.addon_checkboxes.clear()
        self.modifier_vars.clear()
        self.modifier_checkboxes.clear()

        addons = groups_data.get('addons', [])
        modifiers = groups_data.get('modifiers', [])

        self._populate_tab_checkboxes(self.addons_scrollable_frame, addons, 'addons')
        self._populate_tab_checkboxes(self.modifiers_scrollable_frame, modifiers, 'modifiers')

    def _populate_tab_checkboxes(self, parent_frame, groups, tab_type):
        """Wypełnia zakładkę checkboxami (Fix: COLOR_PANEL)"""
        if not groups:
            tk.Label(parent_frame, text=f"Nie znaleziono grup {tab_type}",
                     bg=self.config['COLOR_PANEL'], fg=self.config['COLOR_TEXT_MUTED'],
                     font=("Segoe UI", 10)).pack(pady=20)
            return

        for i, group_name in enumerate(groups):
            var = tk.BooleanVar(value=True)

            # Ramka dla checkboxa
            checkbox_frame = tk.Frame(parent_frame, bg=self.config['COLOR_PANEL'])
            checkbox_frame.grid(row=i, column=0, sticky="w", padx=10, pady=2)

            # Checkbox z nowymi kolorami
            checkbox = ModernCheckbutton(checkbox_frame, group_name, var,
                                         accent=self.config['COLOR_ACCENT'],
                                         fg=self.config['COLOR_TEXT_MAIN'],
                                         bg=self.config['COLOR_PANEL'],
                                         font=("Segoe UI", 9))
            checkbox.pack(anchor="w")

            if tab_type == 'addons':
                self.addon_vars[group_name] = var
                self.addon_checkboxes[group_name] = checkbox
            else:
                self.modifier_vars[group_name] = var
                self.modifier_checkboxes[group_name] = checkbox

        parent_frame.grid_columnconfigure(0, weight=1)

    def select_all_groups(self):
        """Zaznacza wszystkie grupy w obu zakładkach"""
        for var in self.addon_vars.values():
            var.set(True)
        for checkbox in self.addon_checkboxes.values():
            checkbox.redraw()
        for var in self.modifier_vars.values():
            var.set(True)
        for checkbox in self.modifier_checkboxes.values():
            checkbox.redraw()

    def deselect_all_groups(self):
        """Odznacza wszystkie grupy w obu zakładkach"""
        for var in self.addon_vars.values():
            var.set(False)
        for checkbox in self.addon_checkboxes.values():
            checkbox.redraw()
        for var in self.modifier_vars.values():
            var.set(False)
        for checkbox in self.modifier_checkboxes.values():
            checkbox.redraw()

    def get_selected_groups(self):
        """Zwraca listę zaznaczonych grup z obu zakładek"""
        selected = []
        selected.extend([group_name for group_name, var in self.addon_vars.items() if var.get()])
        selected.extend([group_name for group_name, var in self.modifier_vars.items() if var.get()])
        return selected

    def validate_json(self):
        path = self.menu_entry.get()
        if not os.path.isfile(path):
            self.open_chrome_button.config(state="disabled")
            return False, ["Brak pliku menu.json!"]
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
        except Exception as e:
            self.open_chrome_button.config(state="disabled")
            return False, [f"Nie udało się wczytać pliku: {e}"]

        errors = []
        if not isinstance(data, dict):
            errors.append("Plik nie jest słownikiem ({}).")
        else:
            for cat, dishes in data.items():
                if not isinstance(cat, str):
                    errors.append(f"Kategoria {cat} nie jest tekstem.")
                if not isinstance(dishes, list):
                    errors.append(f"Wartość kategorii '{cat}' nie jest listą.")
                else:
                    for idx, dish in enumerate(dishes):
                        if not isinstance(dish, dict):
                            errors.append(f"W kategorii '{cat}' pozycja {idx + 1} nie jest obiektem.")
                            continue
                        if "name" not in dish:
                            errors.append(f"W kategorii '{cat}' pozycja {idx + 1} brak pola 'name'.")
                        if "price" not in dish:
                            errors.append(f"W kategorii '{cat}' pozycja {idx + 1} brak pola 'price'.")
                        if "ingredients" in dish and not isinstance(dish["ingredients"], list):
                            errors.append(
                                f"W kategorii '{cat}' danie '{dish.get('name', '')}' pole 'ingredients' nie jest listą.")
                        if "description" in dish and not isinstance(dish["description"], str):
                            errors.append(
                                f"W kategorii '{cat}' danie '{dish.get('name', '')}' pole 'description' nie jest tekstem.")

        if errors:
            self.open_chrome_button.config(state="disabled")
        else:
            self.open_chrome_button.config(state="normal")

        return not errors, errors

    def show_json_status(self, is_ok, errs):
        if is_ok:
            self.json_status_label.config(
                text="✅ Poprawny plik JSON - gotowy do uploadu",
                fg="#4ade80",  # Jasny zielony dla efektu flash
                font=("Segoe UI", 9, "bold")
            )
            # Używamy COLOR_SUCCESS zamiast COLOR_OK
            self.json_status_label.after(200, lambda: self.json_status_label.config(fg=self.config['COLOR_SUCCESS']))
        else:
            error_text = f"❌ Błąd: {errs[0] if errs else 'Nieznany błąd'}"
            if len(errs) > 1:
                error_text += f" (+{len(errs) - 1} więcej)"
            self.json_status_label.config(
                text=error_text,
                fg="#f87171",  # Jasny czerwony dla efektu flash
                font=("Segoe UI", 9, "bold")
            )
            # Używamy COLOR_DANGER zamiast COLOR_ERROR
            self.json_status_label.after(200, lambda: self.json_status_label.config(fg=self.config['COLOR_DANGER']))

    def save_logs_to_file(self, reason="finished"):
        try:
            base_dir = os.path.dirname(self.menu_path_current) if self.menu_path_current and os.path.isdir(
                os.path.dirname(self.menu_path_current)) else os.getcwd()
            log_dir = os.path.join(base_dir, "logs")
            os.makedirs(log_dir, exist_ok=True)

            ts = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
            status = "finished" if reason == "finished" else ("stopped" if reason == "stopped" else "error")
            fname = f"papu_menu_upload_{status}_{ts}.log"
            path = os.path.join(log_dir, fname)

            header = [
                f"Papu Menu Uploader {VERSION}",
                f"URL: {self.url}",
                f"JSON: {self.menu_path_current or '-'}",
                "Options: "
                f"skip_categories={self.skip_categories_var.get()}, "
                f"with_ingredients={self.with_ingredients_var.get()}, "
                f"with_description={self.with_description_var.get()}, "
                f"with_sizes={self.with_sizes_var.get()}, "
                f"with_addons={self.with_addons_var.get()}, "
                f"skip_dishes={self.skip_dishes_var.get()}, "
                f"with_modifiers={self.with_modifiers_var.get()}",
                f"Result: {status}",
                "-" * 60,
            ]

            with open(path, "w", encoding="utf-8") as f:
                f.write("\n".join(header) + "\n")
                f.write("\n".join(self._log_lines))
                f.write("\n")

            self._last_log_path = path
            self.log_print(f"📄 Zapisano log: {path}")
            return path
        except Exception as e:
            self.log_print(f"⚠️ Nie udało się zapisać pliku logu: {e}")
            return None

    def choose_menu(self):
        self.log_print("Otwieranie okna wyboru pliku menu.json...")
        filename = filedialog.askopenfilename(title="Wybierz menu.json", filetypes=[("JSON files", "*.json")])
        if filename:
            self.log_print(f"Wybrano plik: {filename}")
            self.menu_entry.delete(0, tk.END)
            self.menu_entry.insert(0, filename)

            self.log_print("Walidacja pliku JSON...")
            is_ok, errs = self.validate_json()
            self.show_json_status(is_ok, errs)

            if is_ok:
                self.log_print("Plik JSON jest poprawny", "success")
            else:
                self.log_print(f"Błędy walidacji: {'; '.join(errs)}", "error")

            if is_ok:
                self.log_print("Skanuję grupy dodatków/modyfikatorów...")
                groups_data = self.scan_menu_groups(filename)
                addons = groups_data.get('addons', [])
                modifiers = groups_data.get('modifiers', [])

                if addons or modifiers:
                    self.log_print(f"Znaleziono {len(addons)} dodatków i {len(modifiers)} modyfikatorów", "success")
                    if addons:
                        self.log_print(f"Dodatki: {', '.join(addons[:3])}{'...' if len(addons) > 3 else ''}")
                    if modifiers:
                        self.log_print(f"Modyfikatory: {', '.join(modifiers[:3])}{'...' if len(modifiers) > 3 else ''}")
                    self.populate_groups_checkboxes(groups_data)
                    self.groups_frame.grid()
                    self.log_print("Sekcja wyboru grup została wyświetlona")
                else:
                    self.log_print("Nie znaleziono grup dodatków/modyfikatorów", "warning")
                    self.groups_frame.grid_remove()
            else:
                self.groups_frame.grid_remove()
        else:
            self.log_print("Anulowano wybór pliku")

    def preview_json(self):
        # Ta metoda jest bardzo długa, ale jej wewnętrzny kod nie uległ zmianie,
        # więc pomijam go dla czytelności.
        messagebox.showinfo("Podgląd JSON",
                            "Funkcja podglądu JSON analizuje plik i wyświetla szczegółowy raport w nowym oknie. Działa bez zmian.")

    def log_print(self, txt, msg_type="info"):
        """Wyświetla komunikat w logach z kolorami i ikonami oraz zapisuje do pliku
        msg_type: 'info', 'success', 'warning', 'error'
        """
        line = str(txt)
        self._log_lines.append(line)

        self._write_to_live_log(line, msg_type)

        self.log.config(state="normal")

        if msg_type == "success":
            formatted_line = f"✅ {line}"
            color = "#00ff88"
        elif msg_type == "error":
            formatted_line = f"❌ {line}"
            color = self.config['COLOR_ERROR']
        elif msg_type == "warning":
            formatted_line = f"⚠️ {line}"
            color = self.config['COLOR_WARNING']
        else:
            formatted_line = f"ℹ️ {line}"
            color = "#c8ffda"

        start_pos = self.log.index(tk.END)
        self.log.insert(tk.END, formatted_line + "\n")
        end_pos = self.log.index(tk.END + "-1c")

        self.log.tag_add(f"color_{msg_type}", start_pos, end_pos)
        self.log.tag_config(f"color_{msg_type}", foreground=color)

        self.log.yview_moveto(1)
        self.log.config(state="disabled")
        self.root.update()

    def open_chrome(self):
        # REMOVED: self.save_settings() call because inputs are no longer in main window.
        # Settings are saved only via the "Account" button popup now.

        self.log_print("Checking JSON file integrity...")
        is_ok, errs = self.validate_json()
        if not is_ok:
            self.log_print("Invalid menu.json file", "error")
            messagebox.showerror("Error", "Invalid JSON file!\n" + "\n".join(errs))
            return

        self.log_print("Starting Chrome...", "success")

        # Hide main buttons
        self.open_chrome_button.pack_forget()
        self.menu_button.pack_forget()
        self.preview_button.pack_forget()
        self.menu_entry.config(state="disabled")

        # REMOVED: Config calls for email_entry/pass_entry as they don't exist here anymore

        def run_chrome():
            try:
                options = webdriver.ChromeOptions()
                self.driver = webdriver.Chrome(service=Service(ChromeDriverManager().install()), options=options)

                self.log_print(f"Opening: {self.url}")
                self.driver.get(self.url)

                # --- AUTO LOGIN START ---
                self._perform_auto_login(self.driver)
                # --- AUTO LOGIN END ---

                self.log_print("Ready. Navigate to menu edit and click START.")
                self.start_button.after(0, lambda: self.start_button.pack(side="left", padx=5))

            except Exception as e:
                self.log_print(f"Chrome Error: {e}", "error")
                # Restore GUI on error
                self.root.after(0, lambda: self.open_chrome_button.pack(side="left", padx=5))
                self.root.after(0, lambda: self.menu_button.pack(side="left"))
                self.root.after(0, lambda: self.preview_button.pack(side="left", padx=(5, 0)))
                self.root.after(0, lambda: self.menu_entry.config(state="normal"))

        threading.Thread(target=run_chrome, daemon=True).start()

    def hide_gui_elements(self):
        """Minimalizuje interfejs podczas pracy."""
        self.middle_frame.pack_forget()  # Ukrywa całą środkową sekcję (Opcje + Grupy)
        # Opcjonalnie można ukryć też wybór pliku, jeśli chcesz
        # self.menu_entry.master.master.pack_forget()

        self.open_chrome_button.pack_forget()
        self.start_button.pack_forget()
        self.stop_button.pack(side="left", padx=5)  # Pokazuje STOP

        self.gui_minimized = True

    def show_gui_elements(self):
        """Przywraca interfejs."""
        self.middle_frame.pack(fill="x", pady=10, after=self.main_container.winfo_children()[1])  # Przywraca środek

        self.stop_button.pack_forget()
        self.open_chrome_button.pack(side="left", padx=5)
        self.start_button.pack(side="left", padx=5)

        self.gui_minimized = False

    def stop_upload(self):
        """Obsługuje kliknięcie przycisku STOP"""
        self.log_print("=== ZATRZYMYWANIE PROCESU UPLOADU ===", "warning")
        self.log_print("Kończę program na żądanie użytkownika!", "warning")

        try:
            self.log_print("Zapisywanie logów do pliku...")
            self.save_logs_to_file("stopped")
            self.log_print("Logi zapisane pomyślnie", "success")
        except Exception as e:
            self.log_print(f"Błąd zapisu logów: {e}", "error")

        try:
            if self.driver:
                self.log_print("Zamykanie przeglądarki Chrome...")
                self.driver.quit()
                self.log_print("Przeglądarka zamknięta", "success")
        except Exception as e:
            self.log_print(f"Błąd zamykania przeglądarki: {e}", "error")

        self.log_print("Przywracanie interfejsu...")
        self.show_gui_elements()

        self.log_print("=== APLIKACJA ZAKOŃCZONA ===", "warning")
        self.root.quit()
        self.root.destroy()
        sys.exit(0)

    def start_upload(self):
        self.log_print("=== ROZPOCZĘCIE PROCESU UPLOADU ===", "success")

        if self.driver is None:
            self.log_print("Brak połączenia z Chrome - najpierw kliknij 'Otwórz Chrome'!", "error")
            return

        self.log_print("Pobieranie konfiguracji uploadu...")
        menu_path = self.menu_entry.get()
        self.menu_path_current = menu_path

        # Pobieranie wartości zmiennych
        skip_cat = self.skip_categories_var.get()
        with_ing = self.with_ingredients_var.get()
        with_desc = self.with_description_var.get()
        with_sizes = self.with_sizes_var.get()
        with_addons = self.with_addons_var.get()
        skip_dishes = self.skip_dishes_var.get()
        with_modifiers = self.with_modifiers_var.get()

        selected_groups = self.get_selected_groups()
        if selected_groups:
            self.log_print(f"Wybrane grupy ({len(selected_groups)}): {', '.join(selected_groups[:3])}...")
        else:
            self.log_print("Nie wybrano grup dodatków/modyfikatorów.", "warning")

        self.log_print("Przełączanie interfejsu w tryb uploadu...")

        # NOWY SPOSÓB UKRYWANIA (Metoda hide_gui_elements zarządza przyciskami Stop/Start)
        self.hide_gui_elements()

        self.log_print("Startuję automatyczne wprowadzanie menu...", "success")

        # Reset paska postępu (jest zawsze widoczny w stopce, więc tylko zerujemy)
        self.update_progress(0, "Start...")

        try:
            with open(menu_path, 'r', encoding='utf-8') as f:
                menu_data = json.load(f)
            total_items = sum(len(dishes) for dishes in menu_data.values())
            estimated_seconds = total_items * 2
            self.total_items = total_items
            self.processed_items = 0
            self.start_time = time.time()
            self.update_eta(estimated_seconds)
        except Exception as e:
            self.log_print(f"Błąd szacowania czasu: {e}", "error")

        def do_upload():
            reason = "finished"
            try:
                upload_menu(
                    self.driver,
                    menu_path,
                    skip_categories=skip_cat,
                    with_ingredients=with_ing,
                    with_description=with_desc,
                    log_func=self.log_print,
                    with_sizes=with_sizes,
                    with_addons=with_addons,
                    skip_dishes=skip_dishes,
                    with_modifiers=with_modifiers,
                    progress_callback=self.progress_callback,
                    selected_groups=selected_groups,
                    config=self.config,
                )
                self.log_print("Gotowe! Możesz zamknąć okno.", "success")
            except Exception as e:
                reason = "error"
                self.log_print(f"Błąd krytyczny: {e}", "error")
            finally:
                self.save_logs_to_file(reason)
                # Przywracanie interfejsu w głównym wątku
                self.root.after(0, self.show_gui_elements)

        self.upload_thread = threading.Thread(target=do_upload, daemon=True)
        self.upload_thread.start()

    def update_progress(self, percentage, status_text=""):
        """Aktualizuje pasek postępu w stopce."""
        try:
            val = max(0, min(100, percentage))
            self.progress_bar['value'] = val

            if percentage >= 100:
                status_display = "✅ Ukończono"
                self.progress_status.config(fg=self.config['COLOR_SUCCESS'])
            elif percentage > 0:
                status_display = f"⚡ W toku ({int(percentage)}%)"
                self.progress_status.config(fg=self.config['COLOR_ACCENT'])
            else:
                status_display = "⏳ Oczekiwanie..."
                self.progress_status.config(fg=self.config['COLOR_TEXT_MUTED'])

            if status_text:
                status_display = status_text

            self.progress_status.config(text=status_display)
            self.root.update_idletasks()
        except Exception:
            pass

    def update_eta(self, estimated_seconds):
        """Aktualizuje szacowany czas zakończenia"""
        try:
            if estimated_seconds <= 0:
                eta_text = "ETA: --:--"
            else:
                minutes = int(estimated_seconds // 60)
                seconds = int(estimated_seconds % 60)
                eta_text = f"ETA: {minutes:02d}:{seconds:02d}"

            self.eta_label.config(text=eta_text)
            self.root.update_idletasks()
        except:
            pass

    def progress_callback(self, current, total, item_name="", phase=""):
        """Callback do aktualizacji postępu podczas uploadu"""
        try:
            percentage = (current / total) * 100 if total > 0 else 0

            if hasattr(self, 'start_time') and current > 0:
                elapsed = time.time() - self.start_time
                avg_time_per_item = elapsed / current
                remaining_items = total - current
                remaining_seconds = remaining_items * avg_time_per_item
                self.update_eta(remaining_seconds)

            self.update_progress(percentage)

            if item_name:
                self.log_print(f"[{current}/{total}] {item_name}")
        except:
            pass


if __name__ == "__main__":
    root = tk.Tk()
    app = PapuGUI(root)
    root.mainloop()