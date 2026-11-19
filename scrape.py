"""Agente Tennis Tavolo (versione 1.1 del 19/11/2026, scheda 41)

NOVITÀ della 1.1 (dopo la prima «Solo prova» su GitHub, in cui tutti gli archivi risultavano assenti):
  - le richieste al sito imitano un browser vero (intestazioni complete);
  - ogni file si cerca su DUE indirizzi del sito (con e senza memoria cache);
  - un rifiuto del sito (403, 5xx, pagina non JSON) NON è più scambiato per «archivio non pubblicato»:
    viene segnalato con il codice di risposta, e il lancio diventa rosso;
  - all'inizio una DIAGNOSTICA prova un archivio sicuramente presente (Europe Smash 2026) e stampa
    cosa risponde ogni indirizzo.

Legge dal sito ufficiale WTT (World Table Tennis) i risultati incontro per incontro dei tornei
  Smash, Champions, Star Contender, Contender, WTT Finals, Mondiali e World Cup
a partire dal 1/1/2025 e li scrive nel database Notion «🏓 Agente Tennis Tavolo», senza doppioni.
Prepara anche il file tennistavolo.json (per la futura pagina tennistavolo.html, sessione 3),
che per ora resta solo negli Artifacts del lancio.

Regole decise da Gualtiero (foglio «Tennistavolo LA28 – punti da decidere e verificare»):
  - solo tornei CONCLUSI e già ARCHIVIATI dal sito (ritardo di 1-2 giorni sui tornei in corso);
  - qualificazioni INCLUSE, con la colonna «Tabellone» = «Qualificazione»;
  - esclusi: gare a squadre (anche i Mondiali 2026 di Londra, solo a squadre), Mixed Team World Cup,
    Para, Youth, Veterani, Feeder, Giochi e campionati continentali;
  - vincitore sempre in «Player 1», punteggio dal suo punto di vista;
  - doppi: ID ITTF della coppia = i due codici in ordine crescente con «/» (es. «112620/115543»).

Variabili (i «Secrets» e le scelte del workflow di GitHub):
  NOTION_TOKEN        token della connessione Notion «Agente Squash»
  NOTION_DATABASE_ID  link o codice del database «🏓 Agente Tennis Tavolo»
  DRY_RUN=true        prova: legge sito e Notion ma non scrive nulla
  MODALITA            «aggiungi» (normale) o «completa» (rilegge anche i tornei già caricati)
  TEMPO_MAX_MINUTI    dopo quanti minuti smettere di scrivere e chiudere in ordine (predefinito 110)
  WTT_LOCALE          SOLO PER I COLLAUDI: cartella con file già scaricati al posto del sito
"""
import json
import os
import re
import sys
import time
from collections import Counter
from datetime import date, datetime

import requests

# ------------------------------------------------------------------ impostazioni
ANNO_INIZIO = 2025

# Categorie del calendario WTT (campo EventTypeId) -> valore della colonna «Categoria» in Notion
CATEGORIE = {
    64: "Smash",            # WTT Grand Smash
    65: "Champions",        # WTT Champions
    35: "Star Contender",   # WTT Star Contender
    34: "Contender",        # WTT Contender
    75: "WTT Finals",       # WTT Finals
    37: "Mondiali",         # ITTF World Table Tennis Championships (nel 2026 solo a squadre)
    95: "World Cup",        # ITTF Men's & Women's World Cup (singolari)
}
# Parole che, nel nome del torneo, lo escludono comunque (per sicurezza)
NOMI_ESCLUSI = ("youth", "para ", "veteran", "junior", "masters")

# Nelle categorie qui sotto i gironi («Group») fanno parte del torneo vero e proprio;
# negli altri (Contender, Star Contender, Smash) i gironi sono di qualificazione. Verificato il 19/11/2026.
GIRONI_PRINCIPALI = {"WTT Finals", "World Cup", "Mondiali"}

# Indirizzi del sito WTT (servizi JSON pubblici usati dal sito stesso, nessun login)
WTT = "https://wtt-web-frontdoor-cthahjeqhbh6aqe3.a01.azurefd.net"                  # con memoria cache
WTT_SENZA_CACHE = "https://wtt-web-frontdoor-withoutcache-cqakg0andqf5hchn.a01.azurefd.net"  # senza cache
CALENDARI = [  # si provano in quest'ordine (il 2025 è solo nell'ultimo)
    WTT + "/websitestaticapifiles/general/{anno}_eventcalendar.json",
    WTT_SENZA_CACHE + "/websitestaticapifiles/general/{anno}_eventcalendar.json",
    "https://www.worldtabletennis.com/assets/json/{anno}_eventcalendar.json",
]
ARCHIVI = [  # stesso file su due indirizzi: verificato dal browser il 19/11/2026
    WTT + "/websitearchivedresults/{id}/officialresult/officialresult.json",
    WTT_SENZA_CACHE + "/websitearchivedresults/{id}/officialresult/officialresult.json",
]
ID_DIAGNOSTICA = 3246   # Europe Smash 2026: archivio sicuramente presente (307 incontri)
PAGINA_TORNEO = "https://www.worldtabletennis.com/eventInfo?eventId={id}&selectedTab=Results"
# Intestazioni come quelle di Chrome quando il sito worldtabletennis.com chiede i suoi file
WEB_HEADERS = {
    "User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) "
                   "Chrome/131.0.0.0 Safari/537.36"),
    "Accept": "application/json, text/plain, */*",
    "Accept-Language": "it-IT,it;q=0.9,en;q=0.8",
    "Origin": "https://www.worldtabletennis.com",
    "Referer": "https://www.worldtabletennis.com/",
    "Sec-Fetch-Dest": "empty",
    "Sec-Fetch-Mode": "cors",
    "Sec-Fetch-Site": "cross-site",
}


class SitoRifiuta(Exception):
    """Il sito WTT ha risposto, ma non con il file: rifiuto (403), errore (5xx) o pagina non JSON."""
PAUSA_SITO = 1.0      # secondi di pausa tra una richiesta e l'altra al sito WTT
PAUSA_NOTION = 0.35   # secondi di pausa tra una scrittura e l'altra su Notion
LIMITE_NOTION = 10000  # oltre questo numero di righe una ricerca di Notion non va (schede 29-30)

# Specialità: caratteri 4-11 del documentCode -> sigla
SPECIALITA = {"MSINGLES": "MS", "WSINGLES": "WS", "MDOUBLES": "MD", "WDOUBLES": "WD", "XDOUBLES": "XD"}
GENDER = {"MS": "Men", "MD": "Men", "WS": "Women", "WD": "Women", "XD": "Mixed"}
ORDINE_SPEC = ["MS", "WS", "MD", "WD", "XD"]

# Turni del tabellone principale: caratteri 23-26 del documentCode -> valore di «Turno»
TURNI = {"R128": "Round of 128", "R64-": "Round of 64", "R32-": "Round of 32", "8FNL": "Round of 16",
         "QFNL": "Quarter Final", "SFNL": "Semi Final", "FNL-": "Final"}
ORDINE_TURNI = ["Qualifying Group", "Qualifying Round 1", "Qualifying Round 2", "Qualifying Round 3",
                "Qualifying Round 4", "Qualification Elimination Round", "Group Stage", "Round of 128",
                "Round of 64", "Round of 32", "Round of 16", "Quarter Final", "Semi Final", "Final"]

# Esito scritto in fondo al punteggio WTT («3-0 WO») -> testo in «Score»
ESITI = {"WO": "walkover", "INJ": "ritiro", "RET": "ritiro", "DSQ": "squalifica"}

# Variabili d'ambiente
NOTION_TOKEN = os.getenv("NOTION_TOKEN", "").strip()
_grezzo = os.getenv("NOTION_DATABASE_ID", "").strip().replace("-", "")
_trovato = re.search(r"[0-9a-fA-F]{32}", _grezzo)
DATABASE_ID = _trovato.group(0) if _trovato else _grezzo
DRY_RUN = os.getenv("DRY_RUN", "").strip().lower() == "true"
MODALITA = (os.getenv("MODALITA", "") or "aggiungi").strip().lower()
TEMPO_MAX = float(os.getenv("TEMPO_MAX_MINUTI", "") or 110) * 60
WTT_LOCALE = os.getenv("WTT_LOCALE", "").strip()
FILE_WEB = "tennistavolo.json"

NOTION_HEADERS = {"Authorization": f"Bearer {NOTION_TOKEN}", "Notion-Version": "2022-06-28",
                  "Content-Type": "application/json"}

# Nomi delle colonne nel database (maiuscole/minuscole non contano).
# La colonna «titolo» (Incontro) viene riconosciuta da sola.
COLONNE = {
    "torneo": ["Torneo"], "categoria": ["Categoria"], "disciplina": ["Disciplina"],
    "p1": ["Player 1"], "noc1": ["NOC 1"], "p2": ["Player 2"], "noc2": ["NOC 2"],
    "gender": ["Gender"], "score": ["Score"], "turno": ["Turno"], "tabellone": ["Tabellone"],
    "data": ["Data"], "fonte": ["Fonte"], "id": ["ID Univoco"], "id1": ["ID ITTF 1"], "id2": ["ID ITTF 2"],
}

INIZIO = time.time()
AVVISI = []


def avviso(testo):
    """Annota un avviso: compare subito nel registro e di nuovo nel riepilogo finale."""
    print("  Avviso: " + testo)
    AVVISI.append(testo)


def muori(testo):
    print("ERRORE: " + testo)
    sys.exit(1)


def tempo_scaduto():
    return time.time() - INIZIO > TEMPO_MAX


# ------------------------------------------------------------------ sito WTT
def chiedi(url):
    """Una richiesta al sito WTT (con 3 tentativi se la rete cade).
    Restituisce (codice di risposta, dati JSON oppure None, descrizione breve della risposta)."""
    for tentativo in range(3):
        try:
            r = requests.get(url, headers=WEB_HEADERS, timeout=90)
            time.sleep(PAUSA_SITO)
            break
        except requests.RequestException as e:
            if tentativo == 2:
                return 0, None, f"rete: {type(e).__name__}"
            time.sleep(5)
    tipo = (r.headers.get("Content-Type") or "").split(";")[0]
    inizio = r.text[:80].replace("\n", " ") if r.content else ""
    descrizione = f"{r.status_code} {tipo} «{inizio}»"
    if r.status_code != 200:
        return r.status_code, None, descrizione
    try:
        return 200, r.json(), descrizione
    except ValueError:
        return 200, None, descrizione       # risposta 200 ma non JSON (es. errore XML)


def scarica(urls, nome_locale=None):
    """Scarica un file JSON dal sito WTT, provando gli indirizzi in ordine.
    - Restituisce i dati al primo indirizzo che li dà.
    - Restituisce None se il file NON ESISTE (404, o l'errore XML «BlobNotFound» del sito).
    - Solleva SitoRifiuta se il sito risponde in altro modo (403, 5xx, rete): così un blocco
      dei server di GitHub non viene scambiato per «archivio non pubblicato».
    Con WTT_LOCALE (collaudi) legge invece il file nome_locale da quella cartella."""
    if WTT_LOCALE:
        percorso = os.path.join(WTT_LOCALE, nome_locale or "")
        if not os.path.exists(percorso):
            return None
        with open(percorso, encoding="utf-8") as f:
            return json.load(f)
    problemi = []
    for url in urls:
        codice, dati, descrizione = chiedi(url)
        if dati is not None:
            return dati
        non_esiste = codice == 404 or (codice == 200 and "NotFound" in descrizione) \
            or (codice in (400, 409) and "xml" in descrizione.lower())
        if not non_esiste:
            problemi.append(f"{url.split('/')[2].split('.')[0]}: {descrizione}")
    if problemi:
        raise SitoRifiuta("; ".join(problemi))
    return None


def diagnostica():
    """Prova un archivio sicuramente presente su ogni indirizzo e stampa cosa risponde il sito.
    Restituisce True se almeno un indirizzo dà i dati."""
    if WTT_LOCALE:
        return True
    print(f"\nDiagnostica: archivio di Europe Smash 2026 (id {ID_DIAGNOSTICA}), che esiste di sicuro")
    riuscito = False
    for modello in ARCHIVI:
        url = modello.format(id=ID_DIAGNOSTICA)
        codice, dati, descrizione = chiedi(url)
        esito = f"OK, {len(dati)} incontri" if isinstance(dati, list) else "NESSUN DATO"
        print(f"  {url.split('/')[2]}: {esito} · risposta {descrizione}")
        riuscito = riuscito or isinstance(dati, list)
    if not riuscito:
        avviso("la diagnostica non riesce a leggere l'archivio di prova: il sito WTT rifiuta i server di "
               "GitHub (vedi i codici qui sopra). Manda il rapporto a Claude.")
    return riuscito


def pulisci_nome_torneo(nome):
    """«WTT Champions Macao 2025 Presented by Galaxy …» -> «WTT Champions Macao 2025».
    Toglie anche le virgole (in Notion separerebbero le opzioni) e gli spazi doppi."""
    nome = re.split(r"\s+presented\s+by\s+", nome or "", flags=re.I)[0]
    nome = nome.replace(",", " ")
    return re.sub(r"\s+", " ", nome).strip()[:100]


def calendario(oggi):
    """Tornei delle 7 categorie, dal 2025 a oggi, in ordine di data."""
    tornei = {}
    for anno in range(ANNO_INIZIO, oggi.year + 1):
        try:
            dati = scarica([m.format(anno=anno) for m in CALENDARI], f"cal_{anno}.json")
        except SitoRifiuta as e:
            avviso(f"calendario {anno}: il sito WTT non lo dà ({e})")
            continue
        if not dati:
            avviso(f"calendario {anno} non trovato sul sito WTT")
            continue
        blocco = dati[0] if isinstance(dati, list) else dati
        for e in blocco.get("rows") or []:
            cat = CATEGORIE.get(e.get("EventTypeId"))
            nome = (e.get("EventName") or "").strip()
            if not cat or not e.get("EventId") or any(p in nome.lower() for p in NOMI_ESCLUSI):
                continue
            tornei[int(e["EventId"])] = {
                "id": int(e["EventId"]), "nome": pulisci_nome_torneo(nome), "categoria": cat,
                "inizio": (e.get("StartDateTime") or "")[:10], "fine": (e.get("EndDateTime") or "")[:10],
                "luogo": ", ".join(x for x in (e.get("City"), e.get("Country")) if x),
            }
    return sorted(tornei.values(), key=lambda t: (t["inizio"], t["id"]))


# ------------------------------------------------------------------ lettura di un incontro
def turno_e_tabellone(codice_turno, categoria):
    """Dal codice del turno (es. «QFNL», «RND2», «GP05») ricava il valore di «Turno» e il tabellone."""
    if codice_turno in TURNI:
        return TURNI[codice_turno], "Principale"
    if codice_turno.startswith("RND") and codice_turno[3:].isdigit():
        return f"Qualifying Round {int(codice_turno[3:])}", "Qualificazione"
    if codice_turno.startswith("QER"):
        return "Qualification Elimination Round", "Qualificazione"
    if codice_turno.startswith("GP"):
        if categoria in GIRONI_PRINCIPALI:
            return "Group Stage", "Principale"
        return "Qualifying Group", "Qualificazione"
    return None, None


def partite(testo):
    """«11-5,11-8,5-11,0-0» -> [(11, 5), (11, 8), (5, 11)]: tolte le partite non giocate (0-0)."""
    lista = []
    for pezzo in (testo or "").split(","):
        m = re.match(r"\s*(\d+)\s*-\s*(\d+)\s*$", pezzo)
        if m and (int(m.group(1)), int(m.group(2))) != (0, 0):
            lista.append((int(m.group(1)), int(m.group(2))))
    return lista


def togli_riempitivo(lista):
    """Dopo un ritiro (o in un walkover) il sito scrive le partite mancanti come 11-0 / 0-11.
    Si tolgono quelle IN FONDO all'elenco: restano solo le partite giocate davvero."""
    lista = list(lista)
    while lista and lista[-1] in ((11, 0), (0, 11)):
        lista.pop()
    return lista


def data_iso(testo):
    """«08/16/2026 19:00:00» (mese/giorno/anno, ora locale) -> «2026-08-16»."""
    m = re.match(r"\s*(\d{1,2})/(\d{1,2})/(\d{4})", testo or "")
    if not m:
        return ""
    return f"{m.group(3)}-{int(m.group(1)):02d}-{int(m.group(2)):02d}"


def lato(comp):
    """Un lato dell'incontro: nomi, NOC e codice ITTF (per i doppi i due codici in ordine crescente)."""
    giocatori = comp.get("players") or []
    nomi = " / ".join((p.get("playerName") or "").strip() for p in giocatori if p.get("playerName"))
    codici_noc = []
    for p in giocatori:
        c = (p.get("playerOrgCode") or "").strip()
        if c and c not in codici_noc:
            codici_noc.append(c)
    noc = (comp.get("competitiorOrg") or "").strip() or "/".join(codici_noc)
    ids = [str(p.get("playerId") or "").strip() for p in giocatori]
    ids = [i for i in ids if i]
    ids.sort(key=lambda x: (0, int(x)) if x.isdigit() else (1, x))
    return {"nome": nomi or (comp.get("competitiorName") or "").strip(), "noc": noc,
            "id": "/".join(ids), "n": len(giocatori)}


def leggi_incontro(m, t):
    """Trasforma un incontro dell'archivio WTT in una riga per Notion.
    Restituisce (riga, None) oppure (None, motivo dello scarto)."""
    codice = m.get("documentCode") or ""
    if "TEAM" in codice[:12]:
        return None, "gara a squadre"
    spec = SPECIALITA.get(codice[3:11])
    if not spec:
        return None, "specialità non olimpica"
    if re.match(r"^TTE[MWX](SINGLES|DOUBLES)-{4}[A-Z]", codice):
        return None, "Para"               # es. «TTEMSINGLES----MS8…» = Men's Singles Class 8
    turno, tabellone = turno_e_tabellone(codice[22:26], t["categoria"])
    if not turno:
        return None, f"turno sconosciuto «{codice[22:26]}»"
    mc = m.get("match_card") or {}
    if (mc.get("resultStatus") or m.get("fullResults") or "").upper() != "OFFICIAL":
        return None, "risultato non ufficiale"
    comps = mc.get("competitiors") or []      # (sic) il sito scrive «competitiors»
    casa = next((c for c in comps if c.get("competitorType") == "H"), None)
    ospite = next((c for c in comps if c.get("competitorType") == "A"), None)
    if not casa or not ospite:
        return None, "manca uno dei due lati"
    punteggio = re.match(r"^\s*(\d+)\s*-\s*(\d+)\s*([A-Za-z]*)", mc.get("overallScores") or "")
    if not punteggio:
        return None, "punteggio non leggibile"
    a, b, esito = int(punteggio.group(1)), int(punteggio.group(2)), punteggio.group(3).upper()
    if a == b:
        return None, "incontro non concluso"
    vincitore, sconfitto = (lato(casa), lato(ospite)) if a > b else (lato(ospite), lato(casa))
    if not vincitore["nome"] or not sconfitto["nome"]:
        return None, "nome mancante"
    giochi = partite(mc.get("resultsGameScores") or mc.get("gameScores"))
    if a < b:                                          # il vincitore va sempre per primo
        giochi = [(y, x) for x, y in giochi]
    if not esito:
        testo = f"{max(a, b)}-{min(a, b)} (" + ", ".join(f"{x}-{y}" for x, y in giochi) + ")"
    elif esito == "WO":
        testo = "walkover"
    else:
        veri = togli_riempitivo(giochi)
        if esito in ("INJ", "RET") and not veri:
            testo = "walkover (infortunio)"           # ritirato prima di giocare: vale come walkover
        else:
            testo = ESITI.get(esito, esito.lower())
            if veri:
                testo += " (" + ", ".join(f"{x}-{y}" for x, y in veri) + ")"
    giorno = data_iso((mc.get("matchDateTime") or {}).get("startDateLocal")) or t["fine"]
    return {
        "id": f"WTT|{t['id']}|{codice.rstrip('-')}",
        "p1": vincitore["nome"], "noc1": vincitore["noc"], "p2": sconfitto["nome"], "noc2": sconfitto["noc"],
        "id1": vincitore["id"], "id2": sconfitto["id"],
        "gender": GENDER[spec], "disciplina": spec, "score": testo, "turno": turno, "tabellone": tabellone,
        "torneo": t["nome"], "categoria": t["categoria"], "data": giorno,
        "fonte": PAGINA_TORNEO.format(id=t["id"]),
        "_finale": turno == "Final" and tabellone == "Principale",
    }, None


def incontri_del_torneo(t):
    """Legge l'archivio del torneo. Restituisce (righe, scarti) oppure (None, None) se non è archiviato."""
    dati = scarica([m.format(id=t["id"]) for m in ARCHIVI], f"ev_{t['id']}.json")
    if dati is None:
        return None, None
    righe, scarti = {}, Counter()
    for m in dati if isinstance(dati, list) else []:
        riga, motivo = leggi_incontro(m, t)
        if riga:
            righe[riga["id"]] = riga
        else:
            scarti[motivo] += 1
    for motivo in scarti:
        if motivo.startswith("turno sconosciuto") or motivo in ("punteggio non leggibile", "nome mancante"):
            avviso(f"{t['nome']}: {scarti[motivo]} incontri scartati per {motivo}")
    return list(righe.values()), scarti


# ------------------------------------------------------------------ Notion
def notion(metodo, percorso, **kwargs):
    r = None
    for tentativo in range(5):
        r = requests.request(metodo, "https://api.notion.com/v1" + percorso,
                             headers=NOTION_HEADERS, timeout=60, **kwargs)
        if r.status_code == 429 or r.status_code >= 500:
            time.sleep(float(r.headers.get("Retry-After", 2)) + tentativo * 2)
            continue
        break
    if r.status_code == 404:
        muori("Notion non trova il database «🏓 Agente Tennis Tavolo»: aprilo, ••• > Connessioni, "
              "aggiungi la connessione «Agente Squash» e controlla NOTION_DATABASE_ID.")
    if not r.ok:
        raise RuntimeError(f"Notion ha risposto {r.status_code}: {r.text[:400]}")
    return r.json()


def leggi_schema():
    """Trova le colonne del database per nome. Si ferma se ne manca una."""
    props = notion("GET", f"/databases/{DATABASE_ID}")["properties"]
    per_nome = {n.strip().lower(): (n, p["type"]) for n, p in props.items()}
    mappa, mancanti = {}, []
    for chiave, nomi in COLONNE.items():
        trovata = next((per_nome[x.lower()] for x in nomi if x.lower() in per_nome), None)
        if trovata:
            mappa[chiave] = trovata
        else:
            mancanti.append(nomi[0])
    if mancanti:
        muori("nel database mancano queste colonne: " + ", ".join(mancanti)
              + ". Colonne presenti: " + ", ".join(props.keys()))
    mappa["titolo"] = next((n, p["type"]) for n, p in props.items() if p["type"] == "title")
    return mappa


def testo_semplice(prop):
    tipo = prop.get("type")
    if tipo in ("title", "rich_text"):
        return "".join(x.get("plain_text", "") for x in prop.get(tipo) or [])
    if tipo == "select":
        return (prop.get("select") or {}).get("name", "")
    if tipo == "date":
        return (prop.get("date") or {}).get("start", "") or ""
    if tipo == "url":
        return prop.get("url") or ""
    return ""


def cerca(mappa, filtro, etichetta):
    """Tutte le righe che rispettano il filtro, 100 alla volta. Si ferma a 10.000 righe."""
    righe, cursore = [], None
    while True:
        corpo = {"page_size": 100, "filter": filtro}
        if cursore:
            corpo["start_cursor"] = cursore
        dati = notion("POST", f"/databases/{DATABASE_ID}/query", json=corpo)
        for pagina in dati["results"]:
            p = pagina["properties"]
            riga = {k: testo_semplice(p.get(nome, {})) for k, (nome, _) in mappa.items() if k != "titolo"}
            if riga.get("id"):
                righe.append(riga)
        if len(righe) >= LIMITE_NOTION:
            muori(f"la ricerca «{etichetta}» ha raggiunto {LIMITE_NOTION} righe: oltre Notion non legge. "
                  "Serve dividere la lettura (chiedere a Claude).")
        if not dati.get("has_more"):
            return righe
        cursore = dati["next_cursor"]


def righe_presenti(mappa):
    """Legge il database in 6 ricerche (una per specialità + controllo), per stare sotto le 10.000 righe."""
    colonna = mappa["disciplina"][0]
    tutte = []
    for spec in ORDINE_SPEC:
        parte = cerca(mappa, {"property": colonna, "select": {"equals": spec}}, spec)
        print(f"  {spec}: {len(parte)}")
        tutte += parte
    controllo = {"or": [{"property": colonna, "select": {"is_empty": True}},
                        {"and": [{"property": colonna, "select": {"does_not_equal": s}} for s in ORDINE_SPEC]}]}
    altre = cerca(mappa, controllo, "controllo")
    print(f"  altre (Disciplina vuota o diversa): {len(altre)}")
    return tutte + altre


def valore_notion(tipo, valore):
    valore = "" if valore is None else str(valore)
    if tipo == "title":
        return {"title": [{"text": {"content": valore[:2000]}}]}
    if tipo == "rich_text":
        return {"rich_text": [{"text": {"content": valore[:2000]}}] if valore else []}
    if tipo == "select":
        return {"select": {"name": valore.replace(",", " ")[:100]} if valore else None}
    if tipo == "date":
        return {"date": {"start": valore} if valore else None}
    if tipo == "url":
        return {"url": valore or None}
    raise RuntimeError(f"Tipo di colonna non gestito: {tipo}")


def scrivi_riga(mappa, riga):
    valori = dict(riga)
    valori["titolo"] = f"{riga['p1']} vs {riga['p2']}"
    props = {nome: valore_notion(tipo, valori.get(chiave, "")) for chiave, (nome, tipo) in mappa.items()}
    notion("POST", "/pages", json={"parent": {"database_id": DATABASE_ID}, "properties": props})


# ------------------------------------------------------------------ file per la pagina web
def file_web(tornei, righe, oggi):
    """tennistavolo.json: calendario + tutti gli incontri (formato compatto, come badminton.json)."""
    per_torneo = Counter(r.get("torneo", "") for r in righe)
    elenco = []
    for t in tornei:
        if t["inizio"] > oggi.isoformat():
            stato = "da giocare"
        elif t["fine"] >= oggi.isoformat():
            stato = "in corso"
        else:
            stato = "concluso"
        elenco.append({**t, "stato": stato, "incontri": per_torneo.get(t["nome"], 0)})
    incontri = [[r.get("torneo", ""), r.get("disciplina", ""), r.get("turno", ""), r.get("p1", ""), r.get("noc1", ""),
                 r.get("p2", ""), r.get("noc2", ""), r.get("score", ""), r.get("data", ""), r.get("tabellone", ""),
                 r.get("id1", ""), r.get("id2", "")] for r in righe]
    pos = {n: i for i, n in enumerate(ORDINE_TURNI)}
    incontri.sort(key=lambda x: (x[0], ORDINE_SPEC.index(x[1]) if x[1] in ORDINE_SPEC else 9, pos.get(x[2], 99), x[8]))
    return {"aggiornato": oggi.isoformat(), "versione": "1.1",
            "campi": ["torneo", "disciplina", "turno", "vincitore", "noc_vincitore", "sconfitto", "noc_sconfitto",
                      "punteggio", "data", "tabellone", "id_vincitore", "id_sconfitto"],
            "tornei": elenco, "incontri": incontri}


# ------------------------------------------------------------------ programma principale
def main():
    oggi = date.today()
    print(f"Agente Tennis Tavolo 1.1 · {datetime.now():%d/%m/%Y %H:%M} · "
          f"{'SOLO PROVA (non scrivo nulla)' if DRY_RUN else 'lancio vero'} · modalità {MODALITA}")
    if MODALITA not in ("aggiungi", "completa"):
        muori("MODALITA deve essere «aggiungi» o «completa».")

    # 1. Notion: colonne e righe già presenti (anche in prova, se il token c'è)
    mappa, presenti = None, []
    if NOTION_TOKEN and DATABASE_ID:
        mappa = leggi_schema()
        print("Righe già presenti in Notion:")
        presenti = righe_presenti(mappa)
        print(f"  totale: {len(presenti)}")
    elif not DRY_RUN:
        muori("mancano NOTION_TOKEN o NOTION_DATABASE_ID (controlla i Secrets su GitHub).")
    else:
        print("Notion non letto (manca il token): la prova conta tutto come nuovo.")
    gia = {r["id"] for r in presenti}
    finali_presenti = Counter(r["id"].split("|")[1] for r in presenti
                              if r.get("turno") == "Final" and r.get("tabellone", "Principale") == "Principale"
                              and r["id"].count("|") >= 2)

    # 2. Calendario
    tornei = calendario(oggi)
    conta_cat = Counter(t["categoria"] for t in tornei)
    print(f"\nTornei in calendario dal {ANNO_INIZIO}: {len(tornei)} ("
          + ", ".join(f"{c} {conta_cat[c]}" for c in CATEGORIE.values() if conta_cat[c]) + ")")

    # 2b. Diagnostica: se il sito non dà nemmeno l'archivio di prova, inutile continuare
    if not diagnostica():
        print("\nMi fermo: senza accesso agli archivi non posso leggere nessun torneo.")
        print("Avvisi:\n  - " + "\n  - ".join(AVVISI))
        sys.exit(1)

    # 3. Tornei conclusi: lettura dell'archivio e scrittura in Notion
    nuove_tot = scritte = errori = saltati = non_archiviati = 0
    scarti_tot, per_tabellone = Counter(), Counter()
    righe_web = list(presenti)
    fermato = False
    for t in tornei:
        if t["fine"] >= oggi.isoformat():
            continue                                   # in corso o da giocare: si aspetta l'archivio
        if MODALITA == "aggiungi" and finali_presenti.get(str(t["id"])):
            saltati += 1                               # già caricato tutto (le finali si scrivono per ultime)
            continue
        if fermato:
            break
        print(f"\n{t['categoria']} · {t['nome']} ({t['inizio']} – {t['fine']}) · id {t['id']}")
        try:
            righe, scarti = incontri_del_torneo(t)
        except SitoRifiuta as e:
            avviso(f"{t['nome']}: il sito WTT non dà l'archivio ({e})")
            errori += 1
            continue
        if righe is None:
            non_archiviati += 1
            if (oggi - date.fromisoformat(t["fine"])).days > 10:
                avviso(f"{t['nome']}: finito il {t['fine']} ma ancora senza archivio sul sito WTT (controllare)")
            else:
                print("  non ancora archiviato dal sito: lo rileggo al prossimo lancio")
            continue
        if not righe and set(scarti) == {"gara a squadre"}:
            print(f"  solo gare a squadre ({scarti['gara a squadre']} incontri): escluse, nessuna riga")
            continue
        scarti_tot.update(scarti)
        nuove = [r for r in righe if r["id"] not in gia]
        # ordine di scrittura: per data e turno, e LE FINALI PER ULTIME (sono il segno «torneo completo»)
        pos = {n: i for i, n in enumerate(ORDINE_TURNI)}
        nuove.sort(key=lambda r: (r["_finale"], r["data"], pos.get(r["turno"], 99), r["id"]))
        per_tabellone.update(r["tabellone"] for r in nuove)
        nuove_tot += len(nuove)
        print(f"  incontri validi: {len(righe)} (principale {sum(r['tabellone'] == 'Principale' for r in righe)}, "
              f"qualificazione {sum(r['tabellone'] == 'Qualificazione' for r in righe)}), nuovi: {len(nuove)}"
              + (" · scartati: " + ", ".join(f"{k} {v}" for k, v in scarti.items()) if scarti else ""))
        if righe and not any(r["_finale"] for r in righe):
            avviso(f"{t['nome']}: nessuna finale nell'archivio: il torneo verrà riletto a ogni lancio")
        if DRY_RUN:
            for r in nuove[:8]:
                print(f"  [{r['disciplina']}] {r['turno']} | {r['p1']} ({r['noc1']}, {r['id1'] or '—'}) b. "
                      f"{r['p2']} ({r['noc2']}, {r['id2'] or '—'}) | {r['score']} | {r['data']}")
            righe_web += nuove
            continue
        errori_torneo = 0
        for r in nuove:
            if r["_finale"] and errori_torneo:
                avviso(f"{t['nome']}: finali non scritte per gli errori precedenti; il torneo si rilegge al prossimo lancio")
                break
            if tempo_scaduto() and not r["_finale"]:   # le finali (al massimo 5) si scrivono comunque tutte
                avviso(f"Limite di tempo raggiunto ({TEMPO_MAX / 60:.0f} minuti): mi fermo. "
                       "Rilancia l'agente: riprende da dove si è fermato, senza doppioni.")
                fermato = True
                break
            try:
                scrivi_riga(mappa, r)
                gia.add(r["id"])
                righe_web.append(r)
                scritte += 1
                time.sleep(PAUSA_NOTION)
            except (RuntimeError, requests.RequestException) as e:
                print(f"  Errore su {r['p1']} vs {r['p2']}: {e}")
                errori += 1
                errori_torneo += 1
                if r["_finale"]:
                    avviso(f"{t['nome']}: una finale non è stata scritta. Rilancia l'agente in modalità "
                           "«completa» per recuperarla (scrive solo le righe che mancano).")
        print(f"  scritte: {sum(1 for x in nuove if x['id'] in gia)} su {len(nuove)}")

    # 4. File per la pagina web (solo negli Artifacts del lancio, per ora)
    with open(FILE_WEB, "w", encoding="utf-8") as f:
        json.dump(file_web(tornei, righe_web, oggi), f, ensure_ascii=False, separators=(",", ":"))

    # 5. Riepilogo
    print("\n=================== RIEPILOGO ===================")
    print(f"Tornei saltati perché già completi in Notion: {saltati}")
    print(f"Tornei conclusi ma non ancora archiviati dal sito: {non_archiviati}")
    print(f"Incontri nuovi trovati: {nuove_tot} (principale {per_tabellone['Principale']}, "
          f"qualificazione {per_tabellone['Qualificazione']})")
    if scarti_tot:
        print("Incontri scartati: " + ", ".join(f"{k} {v}" for k, v in scarti_tot.most_common()))
    if DRY_RUN:
        print("PROVA: nessuna scrittura. Con il lancio vero verrebbero scritte le righe nuove qui sopra.")
    else:
        print(f"Righe scritte in Notion: {scritte} · errori: {errori}")
    print(f"{FILE_WEB}: {len(righe_web)} incontri (negli Artifacts del lancio)")
    if AVVISI:
        print(f"\nAvvisi ({len(AVVISI)}):")
        for a in AVVISI:
            print("  - " + a)
    print(f"Durata: {(time.time() - INIZIO) / 60:.1f} minuti")
    if errori:
        sys.exit(1)


if __name__ == "__main__":
    main()
