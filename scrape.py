"""Agente Tennis Tavolo (versione 1.4 del 19/11/2026, scheda 43)

NOVITÀ della 1.4 (sessione 3: pagina tennistavolo.html). Notion funziona esattamente come nella 1.3.
  1. TABELLONI UFFICIALI: per ogni torneo l'agente legge dal sito WTT il tabellone di ogni specialità
     (servizio GetBrackets: ordine delle caselle, teste di serie, qualificati «Q», bye, incontri in
     programma e, nei tornei in corso, i risultati già giocati) e lo mette in tennistavolo.json,
     sezione «tabelloni». Anche il tabellone delle QUALIFICAZIONI (sezione «q»).
     I gironi delle WTT Finals e della World Cup si ricostruiscono dalle righe di Notion
     (Turno = «Group Stage»), con la classifica calcolata dai risultati.
     Il tabellone NON va in Notion.
  2. I tabelloni dei tornei finiti non si rileggono ogni giorno: si riprendono dal tennistavolo.json
     già pubblicato. Si rileggono solo i tornei in corso, quelli che iniziano entro 7 giorni e quelli
     non ancora salvati.
  3. PUBBLICAZIONE: nel lancio vero tennistavolo.json viene salvato nel repository della mappa
     (map-q-la28, serve il secret MAPPA_TOKEN) e si avvia la ripubblicazione del sito.
     Senza MAPPA_TOKEN il file resta solo negli Artifacts, come nella 1.3.
  4. Un tabellone che non si riesce a leggere NON ferma l'agente e non colora di rosso il lancio:
     compare un «Avviso» e si tiene quello già pubblicato, se c'è.

NOVITÀ della 1.3 (terza «Solo prova»: 9.771 incontri letti): controllo di coerenza su ogni incontro.
  Si scarta, con un avviso, l'incontro in cui la scheda del sito non corrisponde al codice
  (specialità diversa, numero di giocatori sbagliato, data prima dell'inizio del torneo):
  nell'archivio di Europe Smash 2026 il sito ha messo 3 partite di un altro torneo.

NOVITÀ della 1.2 (seconda «Solo prova»: il sito rispondeva 200 ma con il file compresso Brotli):
  - apre i file compressi Brotli (nuovo pacchetto «brotli» in requirements.txt), gzip e zlib;
  - la diagnostica distingue «risposta ricevuta ma non leggibile» da «rifiuto del sito».

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
  MAPPA_TOKEN         token GitHub che può scrivere su map-q-la28 (novità 1.4; facoltativo:
                      senza, Notion si aggiorna lo stesso ma la pagina web no)
  WTT_LOCALE          SOLO PER I COLLAUDI: cartella con file già scaricati al posto del sito
"""
import base64
import gzip
import json
import os
import re
import sys
import time
import zlib
from collections import Counter
from datetime import date, datetime, timedelta

import requests

try:
    import brotli          # pacchetto per aprire i file compressi Brotli (in requirements.txt)
except ImportError:
    brotli = None

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
    "Accept-Encoding": "gzip, deflate, br",
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
# Come il sito chiama ogni specialità nella scheda dell'incontro (subEventName): serve al controllo di coerenza
NOMI_SPECIALITA = {"MS": "Men's Singles", "WS": "Women's Singles", "MD": "Men's Doubles",
                   "WD": "Women's Doubles", "XD": "Mixed Doubles"}
ORDINE_SPEC = ["MS", "WS", "MD", "WD", "XD"]

# Turni del tabellone principale: caratteri 23-26 del documentCode -> valore di «Turno»
TURNI = {"R128": "Round of 128", "R64-": "Round of 64", "R32-": "Round of 32", "8FNL": "Round of 16",
         "QFNL": "Quarter Final", "SFNL": "Semi Final", "FNL-": "Final"}
ORDINE_TURNI = ["Qualifying Group", "Qualifying Round 1", "Qualifying Round 2", "Qualifying Round 3",
                "Qualifying Round 4", "Qualification Elimination Round", "Group Stage", "Round of 128",
                "Round of 64", "Round of 32", "Round of 16", "Quarter Final", "Semi Final", "Final"]

# Esito scritto in fondo al punteggio WTT («3-0 WO») -> testo in «Score»
ESITI = {"WO": "walkover", "INJ": "ritiro", "RET": "ritiro", "DSQ": "squalifica"}

# ------------------------------------------------------------------ impostazioni dei tabelloni (novità 1.4)
# Servizio del sito WTT che disegna il «Draw» (verificato dal browser il 19/11/2026):
#   GetBrackets/{id torneo}/{codice della specialità lungo 42 caratteri, es. «TTEMSINGLES» + 31 trattini}
# Risponde 204 (nessun contenuto) se quella specialità non ha tabellone (es. doppi dei Champions).
WTT_API = "https://wtt-website-api-vm-frontdoor-hhaec5epbhdyfugz.a01.azurefd.net/liveeventsapi/api/cms"
CODICE_SPEC = {"MS": "TTEMSINGLES", "WS": "TTEWSINGLES", "MD": "TTEMDOUBLES", "WD": "TTEWDOUBLES",
               "XD": "TTEXDOUBLES"}
# codice del turno nel tabellone del sito -> sigla nella pagina (le qualificazioni RND1, RND2... -> Q1, Q2...)
SIGLA_TURNO = {"R128": "R128", "R64-": "R64", "R32-": "R32", "8FNL": "R16", "QFNL": "QF", "SFNL": "SF",
               "FNL-": "Final"}
GIORNI_ANTICIPO_TABELLONE = 7     # il tabellone esce qualche giorno prima dell'inizio del torneo
# Incontri attesi quando il tabellone non c'è (solo per l'anello della pagina; stime)
ATTESI_PREDEFINITI = {"Smash": 300, "Champions": 62, "Star Contender": 250, "Contender": 200,
                      "WTT Finals": 45, "Mondiali": 440, "World Cup": 126}
# Formato di una casella del tabellone in tennistavolo.json (una lista, per occupare poco spazio),
# identico a badminton.json:
#   [colonna, posizione, squadra_a, testa_a, squadra_b, testa_b, vincitore, stato, esito, set, data]
#   - colonna: 0 = primo turno; nei gironi colonna = giornata; posizione: 0 = in alto;
#   - squadra_a / squadra_b: numero nell'elenco «squadre» del torneo, -1 = vuota (bye o da definire);
#   - testa_a / testa_b: testa di serie («1»), «Q» = arrivato dalle qualificazioni, oppure «»;
#   - vincitore: 1 = squadra_a, 2 = squadra_b, 0 = da giocare;
#   - stato: «F» = finito, «N» = da giocare;
#   - esito: «» (normale), «walkover», «ritiro», «squalifica»;
#   - set: le partite dal punto di vista di squadra_a, es. «11-7 9-11 11-5 11-8»;
#   - data: giorno dell'incontro (AAAA-MM-GG) o «».
CAMPI_CASELLA = ["colonna", "posizione", "squadra_a", "testa_a", "squadra_b", "testa_b",
                 "vincitore", "stato", "esito", "set", "data"]
MAPPA_REPO = "vier80/map-q-la28"     # repository della mappa (pagine web)
MAPPA_WORKFLOW = "aggiorna.yml"      # workflow che ripubblica il sito

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
MAPPA_TOKEN = os.getenv("MAPPA_TOKEN", "").strip()       # novità 1.4
VERSIONE = "1.4"

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
    compressione = r.headers.get("Content-Encoding") or "nessuna"
    inizio = testo_leggibile(r.content)[:80].replace("\n", " ")
    descrizione = f"{r.status_code} {tipo} (compressione: {compressione}) «{inizio}»"
    if r.status_code != 200:
        return r.status_code, None, descrizione
    dati = decodifica(r.content)
    return 200, dati, descrizione            # dati = None se la risposta non è JSON (es. errore XML)


def apri_compressione(contenuto):
    """Restituisce il contenuto decompresso (Brotli, gzip o zlib) oppure quello originale."""
    for apri in ([brotli.decompress] if brotli else []) + [gzip.decompress, zlib.decompress]:
        try:
            return apri(contenuto)
        except Exception:
            continue
    return contenuto


def testo_leggibile(contenuto):
    """L'inizio della risposta come testo, decompresso se serve (per il registro e per riconoscere
    l'errore XML «BlobNotFound» anche quando arriva compresso)."""
    try:
        return contenuto.decode("utf-8")
    except UnicodeDecodeError:
        return apri_compressione(contenuto).decode("utf-8", errors="replace")


def decodifica(contenuto):
    """Trasforma la risposta del sito in dati JSON.
    Il sito WTT manda i suoi file COMPRESSI con il formato Brotli (lo stesso che usa il browser),
    a volte senza dirlo nelle intestazioni: in quel caso la libreria requests non li apre da sola
    e il testo sembra fatto di caratteri strani («[6CQA…»; prova su GitHub del 19/11/2026).
    Si prova quindi: testo normale, poi Brotli, poi gzip, poi zlib. None se nessuno funziona."""
    tentativi = [lambda b: b]
    if brotli:
        tentativi.append(brotli.decompress)
    tentativi += [gzip.decompress, zlib.decompress]
    for apri in tentativi:
        try:
            return json.loads(apri(contenuto).decode("utf-8-sig"))
        except Exception:                    # formato sbagliato: si prova il successivo
            continue
    return None


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
    print(f"  pacchetto brotli: {'presente' if brotli else 'MANCANTE (controlla requirements.txt)'}")
    riuscito, risposte_200 = False, 0
    for modello in ARCHIVI:
        url = modello.format(id=ID_DIAGNOSTICA)
        codice, dati, descrizione = chiedi(url)
        esito = f"OK, {len(dati)} incontri" if isinstance(dati, list) else "NESSUN DATO"
        print(f"  {url.split('/')[2]}: {esito} · risposta {descrizione}")
        riuscito = riuscito or isinstance(dati, list)
        risposte_200 += codice == 200
    if not riuscito and risposte_200:
        avviso("la diagnostica riceve l'archivio di prova (risposta 200) ma non riesce ad aprirlo "
               "(formato o compressione sconosciuti). Manda il rapporto a Claude.")
    elif not riuscito:
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
    # Controllo di coerenza (novità 1.3): nell'archivio di Europe Smash 2026 il sito ha messo, sotto il codice
    # di 3 partite di Malmö, partite di un altro torneo (altra specialità, giocatori sbagliati, data precedente).
    incoerenza = None
    descrizione = (mc.get("subEventName") or mc.get("subEventDescription") or "").strip()
    if descrizione and not descrizione.lower().startswith(NOMI_SPECIALITA[spec].lower()):
        incoerenza = f"la scheda dice «{descrizione}»"
    elif any(len(c.get("players") or []) != (2 if spec in ("MD", "WD", "XD") else 1) for c in (casa, ospite)):
        incoerenza = "numero di giocatori sbagliato per la specialità"
    else:
        giorno_scheda = data_iso((mc.get("matchDateTime") or {}).get("startDateLocal"))
        if giorno_scheda and t.get("inizio") and \
                (date.fromisoformat(t["inizio"]) - date.fromisoformat(giorno_scheda)).days > 1:
            incoerenza = f"data {giorno_scheda} prima dell'inizio del torneo"
    if incoerenza:
        avviso(f"{t['nome']}: scartato {codice.rstrip('-')} ({casa.get('competitiorName')} – "
               f"{ospite.get('competitiorName')}): dato incoerente del sito, {incoerenza}")
        return None, "dato incoerente del sito"
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


# ------------------------------------------------------------------ tabelloni ufficiali (novità 1.4)
class Squadre:
    """Elenco delle squadre (giocatori o coppie) di un torneo: ognuna una volta sola.

    Ogni squadra è [nome, NOC, codice ITTF]; nelle caselle del tabellone si scrive solo il suo numero.
    Il codice ITTF di una coppia è quello delle righe di Notion: i due codici in ordine crescente
    separati da «/» (es. «132992/135977»). Serve alla pagina per trovare l'ELO.
    """

    def __init__(self, lista=None):
        self.lista, self.indice = [], {}
        for s in lista or []:                    # elenco già pubblicato (per aggiungere i gironi)
            self.aggiungi(*s)

    def aggiungi(self, nome, noc, codice):
        nome = re.sub(r"\s+", " ", nome or "").strip()
        if not nome:
            return -1
        chiave = codice or nome
        if chiave not in self.indice:
            self.indice[chiave] = len(self.lista)
            self.lista.append([nome, noc or "", codice or ""])
        return self.indice[chiave]


def ordina_codici(codici):
    """Codici ITTF in ordine numerico crescente, uniti con «/» (come nelle colonne ID ITTF 1 e 2)."""
    codici = [str(c).strip() for c in codici if str(c or "").strip()]
    codici.sort(key=lambda x: (0, int(x)) if x.isdigit() else (1, x))
    return "/".join(codici)


def squadra_del_tabellone(posto, squadre):
    """Numero della squadra di un lato di una casella del tabellone (-1 = bye o da definire).

    Il sito scrive Code = «BYE» per il passaggio diretto, «TBD» per l'avversario non ancora noto,
    «WO»/«INJ» per chi non si è presentato o si è ritirato (ma in quel caso Competitor c'è ancora).
    """
    comp = posto.get("Competitor") or {}
    if "BYE" in {(posto.get("Code") or "").strip().upper(), (comp.get("Organization") or "").strip().upper(),
                 ((comp.get("Description") or {}).get("TeamName") or "").strip().upper()}:
        return -1                                       # passaggio diretto (a volte il sito mette un «atleta» BYE)
    atleti = sorted((comp.get("Composition") or {}).get("Athlete") or [], key=lambda a: a.get("Order") or 0)
    if not atleti:
        return -1
    nomi, nocs, codici = [], [], []
    for a in atleti:
        d = a.get("Description") or {}
        nomi.append(f"{(d.get('FamilyName') or '').strip()} {(d.get('GivenName') or '').strip()}".strip())
        noc = (d.get("Organization") or "").strip()
        if noc and noc not in nocs:
            nocs.append(noc)
        codici.append(d.get("IfId") or a.get("Code") or "")
    noc = "/".join(nocs) or (comp.get("Organization") or "").strip()
    return squadre.aggiungi(" / ".join(n for n in nomi if n), noc, ordina_codici(codici))


def testa_di_serie(posto, teste_vere):
    """Testa di serie da mostrare: il numero solo se è davvero una testa di serie.
    Il sito dà un numero a tutti (è la posizione d'ingresso): conta solo se ≤ NoOfSeeds del tabellone.
    «Q» = giocatore arrivato dalle qualificazioni (QualifierType «Q» o «q»)."""
    comp = posto.get("Competitor") or {}
    try:
        seme = int(comp.get("Seed") or 0)
    except (TypeError, ValueError):
        seme = 0
    if 0 < seme <= teste_vere:
        return str(seme)
    if (comp.get("QualifierType") or "").upper() == "Q":
        return "Q"
    return ""


def partite_del_tabellone(risultato):
    """«3-1 (11:7,9:11,11:5,11:8,0:0)» -> [(11, 7), (9, 11), (11, 5), (11, 8)] (tolte le partite 0:0)."""
    m = re.search(r"\((.*)\)", risultato or "")
    lista = []
    for pezzo in (m.group(1) if m else "").split(","):
        x = re.match(r"\s*(\d+)\s*[:\-]\s*(\d+)\s*$", pezzo)
        if x and (int(x.group(1)), int(x.group(2))) != (0, 0):
            lista.append((int(x.group(1)), int(x.group(2))))
    return lista


def casella_del_tabellone(colonna, voce, squadre, teste_vere):
    """Una casella del tabellone nel formato di CAMPI_CASELLA. Il lato con Pos = 1 è squadra_a."""
    posti = sorted(voce.get("CompetitorPlace") or [], key=lambda c: c.get("Pos") or 0)[:2]
    while len(posti) < 2:
        posti.append({})
    lati = [squadra_del_tabellone(c, squadre) for c in posti]
    teste = [testa_di_serie(c, teste_vere) if lati[i] >= 0 else "" for i, c in enumerate(posti)]
    wlt = [(c.get("Wlt") or "").upper() for c in posti]
    vincitore = 1 if wlt[0] == "W" else 2 if wlt[1] == "W" else 0
    giochi = partite_del_tabellone(voce.get("Result"))       # dal punto di vista di Pos 1 (verificato)
    esito = ""
    irm = {(c.get("Irm") or "").upper() for c in posti} - {"", "OK"}
    if vincitore and irm:
        if "WO" in irm:                       # non presentato: le partite 11-0 sono riempitivo
            esito, giochi = "walkover", []
        elif irm & {"INJ", "RET"}:            # ritiro: tolgo le partite di riempitivo in fondo
            giochi = togli_riempitivo(giochi)
            esito = "ritiro" if giochi else "walkover"
        elif "DSQ" in irm:
            esito = "squalifica"
        else:
            esito = sorted(irm)[0].lower()
    try:
        posizione = int(voce.get("Position") or voce.get("Order") or 1) - 1
    except (TypeError, ValueError):
        posizione = 0
    return [colonna, posizione, lati[0], teste[0], lati[1], teste[1], vincitore,
            "F" if vincitore else "N", esito, " ".join(f"{a}-{b}" for a, b in giochi),
            (voce.get("Date") or "")[:10]]


def eliminazione(blocco, squadre):
    """Un tabellone a eliminazione diretta (principale o qualificazioni): {"misura", "turni", "c"}.
    Le colonne vanno dal turno più numeroso (colonna 0) alla finale."""
    turni = [t for t in blocco.get("BracketItems") or [] if t.get("BracketItem")]
    turni.sort(key=lambda t: -len(t["BracketItem"]))
    teste_vere = int(blocco.get("NoOfSeeds") or 0)
    caselle, sigle = [], []
    for colonna, t in enumerate(turni):
        codice = (t.get("Code") or "").strip()
        sigle.append(SIGLA_TURNO.get(codice) or ("Q" + codice[3:].rstrip("-") if codice.startswith("RND")
                                                  else codice.rstrip("-")))
        for voce in t["BracketItem"]:
            caselle.append(casella_del_tabellone(colonna, voce, squadre, teste_vere))
    caselle.sort(key=lambda c: (c[0], c[1]))
    return {"misura": 2 * len(turni[0]["BracketItem"]) if turni else 0, "turni": sigle, "c": caselle}


def scarica_tabellone(evento, spec):
    """Dati di GetBrackets per un torneo e una specialità.
    None = il sito non ha quel tabellone (204 o 404, es. i doppi dei Champions);
    SitoRifiuta = il sito ha risposto in altro modo (403, 5xx, rete)."""
    if WTT_LOCALE:                                       # collaudi: file br_{id}_{MSINGLES...}.json
        percorso = os.path.join(WTT_LOCALE, f"br_{evento}_{CODICE_SPEC[spec][3:]}.json")
        if not os.path.exists(percorso):
            return None
        with open(percorso, encoding="utf-8") as f:
            dati = json.load(f)
        return dati if isinstance(dati, dict) and dati.get("Competition") else None
    codice, dati, descrizione = chiedi(f"{WTT_API}/GetBrackets/{evento}/{CODICE_SPEC[spec].ljust(42, '-')}")
    if codice in (204, 404):
        return None
    if codice == 200 and isinstance(dati, dict):
        return dati if (dati.get("Competition") or {}).get("Bracket") else None
    if codice == 200 and dati is None and "«»" in descrizione:
        return None                                      # risposta vuota
    raise SitoRifiuta(descrizione)


def leggi_tabelloni(t):
    """Tutti i tabelloni di un torneo: {"id", "completo", "attesi", "squadre", "spec": {"MS": {...}, ...}}.

    Per ogni specialità:
      - tabellone a eliminazione: {"tipo": "E", "misura", "turni", "c"};
      - con gironi (WTT Finals, World Cup): {"tipo": "G", ...} con semifinali/finale o ottavi... in "c";
        i gironi ("gironi") si aggiungono dopo, dalle righe di Notion (aggiungi_gironi);
      - qualificazioni a eliminazione, se ci sono: "q": {"misura", "turni", "c"};
        qualificazioni a gironi: "q_gironi": true (la pagina le mostra solo nell'elenco).
    "attesi" = incontri che avrà il torneo = TotalMatchesForSubEvent del sito meno i bye.
    """
    squadre, spec, attesi = Squadre(), {}, 0
    for s in ORDINE_SPEC:
        dati = scarica_tabellone(t["id"], s)
        if not dati:
            continue
        voce = None
        n = int(dati.get("TotalMatchesForSubEvent") or 0)
        for blocco in (dati.get("Competition") or {}).get("Bracket") or []:
            n -= int(blocco.get("NoOfByes") or 0)
            codice = (blocco.get("Code") or "").upper()
            if codice == "MAIN":
                voce = {"tipo": "G" if blocco.get("GroupMatches") else "E", **eliminazione(blocco, squadre)}
            elif codice == "PREL":
                if blocco.get("GroupMatches"):
                    spec.setdefault("_q_gironi", set()).add(s)
                else:
                    spec.setdefault("_q", {})[s] = eliminazione(blocco, squadre)
        if voce:
            spec[s] = voce
            attesi += max(n, 0)
    for s, q in spec.pop("_q", {}).items():
        if s in spec:
            spec[s]["q"] = q
    for s in spec.pop("_q_gironi", set()):
        if s in spec:
            spec[s]["q_gironi"] = True
    if not spec:
        raise ValueError("nessun tabellone pubblicato")
    tutte = [c for v in spec.values() for c in v["c"] + (v.get("q") or {}).get("c", [])]
    completo = bool(tutte) and all(c[7] == "F" for c in tutte)
    return {"id": t["id"], "completo": completo, "attesi": attesi, "squadre": squadre.lista,
            "spec": {s: spec[s] for s in ORDINE_SPEC if s in spec}}


def tabelloni_aggiornati(tornei, vecchi, oggi):
    """Tabelloni da mettere in tennistavolo.json, per nome del torneo.
    Rilegge dal sito solo ciò che può essere cambiato; il resto lo riprende da `vecchi`
    (la sezione «tabelloni» del tennistavolo.json già pubblicato)."""
    nuovi, letti, ripresi, rifiuti = {}, 0, 0, 0
    limite = (oggi + timedelta(days=GIORNI_ANTICIPO_TABELLONE)).isoformat()
    print("\nTabelloni ufficiali (ordine, teste di serie, qualificazioni):")
    for t in tornei:
        if t["inizio"] > limite:
            continue
        vecchio = vecchi.get(t["nome"]) if isinstance(vecchi, dict) else None
        if vecchio and vecchio.get("completo") and vecchio.get("id") == t["id"]:
            nuovi[t["nome"]] = vecchio                   # torneo finito e già salvato: non lo rileggo
            ripresi += 1
            continue
        if tempo_scaduto():
            if vecchio:
                nuovi[t["nome"]] = vecchio
            avviso(f"{t['nome']}: tabellone non riletto per il limite di tempo")
            continue
        try:
            tab = leggi_tabelloni(t)
            letti += 1
            # finito da più di 3 giorni: lo considero chiuso anche se qualche casella è rimasta «da giocare»
            if t["fine"] < (oggi - timedelta(days=3)).isoformat():
                tab["completo"] = True
            nuovi[t["nome"]] = tab
            print(f"  {t['nome']}: " + ", ".join(
                f"{s} {'gironi + ' if v['tipo'] == 'G' else ''}{v['misura']}"
                + (f" (qualif. {v['q']['misura']})" if v.get("q") else "") for s, v in tab["spec"].items()))
        except SitoRifiuta as e:
            rifiuti += 1
            if vecchio:
                nuovi[t["nome"]] = vecchio
            avviso(f"{t['nome']}: tabellone non letto, il sito WTT ha risposto {e}"
                   + ("; tengo quello già pubblicato" if vecchio else ""))
        except ValueError:
            if vecchio:
                nuovi[t["nome"]] = vecchio
            if t["inizio"] > oggi.isoformat():
                print(f"  {t['nome']}: tabellone non ancora pubblicato")
            elif t["categoria"] == "Mondiali":
                print(f"  {t['nome']}: nessun tabellone individuale (Mondiali a squadre)")
            else:
                avviso(f"{t['nome']}: nessun tabellone sul sito WTT")
        except (KeyError, TypeError, IndexError) as e:
            if vecchio:
                nuovi[t["nome"]] = vecchio
            avviso(f"{t['nome']}: tabellone in un formato inatteso ({type(e).__name__}: {e})")
    print(f"  Letti dal sito: {letti}; ripresi da {FILE_WEB} già pubblicato: {ripresi}"
          + (f"; rifiutati dal sito: {rifiuti}" if rifiuti else ""))
    return nuovi


def numero_partite(score):
    """«3-2 (11-6, 10-12, ...)» -> [(11, 6), (10, 12), ...] dal punto di vista del vincitore (Player 1)."""
    m = re.search(r"\((.*)\)", score or "")
    lista = []
    for pezzo in (m.group(1) if m else "").split(","):
        x = re.match(r"\s*(\d+)\s*-\s*(\d+)\s*$", pezzo)
        if x:
            lista.append((int(x.group(1)), int(x.group(2))))
    return lista


def aggiungi_gironi(tabelloni, righe):
    """Gironi delle WTT Finals e della World Cup (tabelloni di tipo «G»), ricostruiti dalle righe di Notion.

    Il sito dà nel tabellone solo la fase a eliminazione: gli incontri dei gironi sono in Notion
    (Turno = «Group Stage»), con il codice del girone nell'ID Univoco («…GP02000600» = girone 2,
    incontro 6). La classifica è calcolata qui: vittorie, poi differenza partite, poi differenza punti;
    tra due giocatori pari per vittorie decide lo scontro diretto.
    Formato di un girone: {"nome", "classifica", "c"}; riga di classifica:
    [posizione, squadra, giocati, vinti, persi, partite vinte, partite perse, punti fatti, punti subiti,
     1 se è passato alla fase a eliminazione altrimenti 0].
    """
    per_torneo = {}
    for r in righe:
        if r.get("turno") != "Group Stage" or (r.get("tabellone") or "Principale") != "Principale":
            continue
        parti = (r.get("id") or "").split("|")
        codice = parti[2] if len(parti) >= 3 else ""
        m = re.match(r"GP(\d+)(\d{4})", codice[22:30])
        if not m:
            continue
        per_torneo.setdefault((r.get("torneo"), r.get("disciplina")), []).append(
            (int(m.group(1)), int(m.group(2)), r))
    for nome, tab in tabelloni.items():
        for s, voce in (tab.get("spec") or {}).items():
            voce.pop("gironi", None)
            if voce.get("tipo") != "G":
                continue
            incontri = per_torneo.get((nome, s), [])
            if not incontri:
                continue
            squadre = Squadre(tab.get("squadre"))
            passati = {c[i] for c in voce.get("c", []) if c[0] == 0 for i in (2, 4) if c[i] >= 0}
            gironi = {}
            for g, num, r in incontri:
                gironi.setdefault(g, []).append((num, r))
            voce["gironi"] = []
            for g in sorted(gironi):
                lista = sorted(gironi[g], key=lambda x: x[0])
                stat, scontri = {}, {}
                caselle = []
                for num, r in lista:
                    a = squadre.aggiungi(r.get("p1"), r.get("noc1"), r.get("id1"))   # vincitore
                    b = squadre.aggiungi(r.get("p2"), r.get("noc2"), r.get("id2"))
                    score = r.get("score") or ""
                    esito = "" if re.match(r"^\d+-\d+", score) else score.split(" ")[0]   # walkover, ritiro...
                    giochi = numero_partite(score)
                    for sq in (a, b):
                        stat.setdefault(sq, [0, 0, 0, 0, 0, 0, 0])   # giocati, vinti, persi, pv, pp, punti f, punti s
                    stat[a][0] += 1; stat[a][1] += 1; stat[b][0] += 1; stat[b][2] += 1
                    for x, y in giochi:
                        stat[a][3] += x > y; stat[a][4] += y > x; stat[b][3] += y > x; stat[b][4] += x > y
                        stat[a][5] += x; stat[a][6] += y; stat[b][5] += y; stat[b][6] += x
                    scontri[(a, b)] = a
                    scontri[(b, a)] = a
                    caselle.append([num, a, b, esito, " ".join(f"{x}-{y}" for x, y in giochi), r.get("data", "")])
                ordine = sorted(stat, key=lambda q: (-stat[q][1], -(stat[q][3] - stat[q][4]), -(stat[q][5] - stat[q][6])))
                for i in range(len(ordine) - 1):        # due pari per vittorie: decide lo scontro diretto
                    x, y = ordine[i], ordine[i + 1]
                    pari = [q for q in ordine if stat[q][1] == stat[x][1]]
                    if len(pari) == 2 and y in pari and x in pari and scontri.get((x, y)) == y:
                        ordine[i], ordine[i + 1] = y, x
                classifica = [[k + 1, q, *stat[q], 1 if q in passati else 0] for k, q in enumerate(ordine)]
                per_giornata = max(1, len(stat) // 2)
                righe_c, contatore = [], {}
                for num, a, b, esito, testo, data in caselle:
                    giornata = (num - 1) // per_giornata
                    pos = contatore.get(giornata, 0)
                    contatore[giornata] = pos + 1
                    righe_c.append([giornata, pos, a, "", b, "", 1, "F", esito, testo, data])
                voce["gironi"].append({"nome": f"Girone {g}", "classifica": classifica, "c": righe_c})
            tab["squadre"] = squadre.lista


def incontri_attesi(tab, categoria):
    """Quanti incontri avrà il torneo (per l'anello della pagina)."""
    if tab and tab.get("attesi"):
        return tab["attesi"]
    return ATTESI_PREDEFINITI.get(categoria, 200)


# ------------------------------------------------------------------ file per la pagina web
def file_web(tornei, righe, oggi, tabelloni=None):
    """tennistavolo.json: calendario + tutti gli incontri + tabelloni (stesso formato di badminton.json).

    Novità 1.4: gli incontri hanno i 9 campi di badminton.json (senza tabellone e codici ITTF, che la
    pagina non usa: il file resta più leggero); ogni torneo ha "id", "url" e "attesi"; c'è la sezione
    «tabelloni». Un torneo concluso senza incontri e senza tabelloni individuali (i Mondiali 2026,
    solo a squadre) non viene messo nella pagina.
    """
    tabelloni = tabelloni or {}
    per_torneo = Counter(r.get("torneo", "") for r in righe)
    elenco = []
    for t in tornei:
        if t["inizio"] > oggi.isoformat():
            stato = "da giocare"
        elif t["fine"] >= oggi.isoformat():
            stato = "in corso"
        else:
            stato = "concluso"
        tab = tabelloni.get(t["nome"])
        if stato == "concluso" and not per_torneo.get(t["nome"]) and not (tab and tab.get("spec")):
            continue                                       # es. Mondiali 2026 a squadre
        elenco.append({"nome": t["nome"], "id": t["id"], "categoria": t["categoria"], "inizio": t["inizio"],
                       "fine": t["fine"], "luogo": t.get("luogo", ""), "url": PAGINA_TORNEO.format(id=t["id"]),
                       "stato": stato, "incontri": per_torneo.get(t["nome"], 0),
                       "attesi": incontri_attesi(tab, t["categoria"])})
    nomi = {t["nome"] for t in elenco}
    incontri = [[r.get("torneo", ""), r.get("disciplina", ""), r.get("turno", ""), r.get("p1", ""), r.get("noc1", ""),
                 r.get("p2", ""), r.get("noc2", ""), r.get("score", ""), r.get("data", "")]
                for r in righe if r.get("torneo", "") in nomi]
    pos = {n: i for i, n in enumerate(ORDINE_TURNI)}
    incontri.sort(key=lambda x: (x[0], ORDINE_SPEC.index(x[1]) if x[1] in ORDINE_SPEC else 9, pos.get(x[2], 99), x[8]))
    return {"aggiornato": oggi.isoformat(), "versione": VERSIONE,
            "stagioni": sorted({t["inizio"][:4] for t in elenco if t["inizio"]}),
            "campi": ["torneo", "disciplina", "turno", "vincitore", "noc_vincitore", "sconfitto", "noc_sconfitto",
                      "punteggio", "data"],
            "tornei": elenco, "incontri": incontri, "campi_casella": CAMPI_CASELLA,
            "tabelloni": {k: v for k, v in sorted(tabelloni.items()) if k in nomi}}


# ------------------------------------------------------------------ pubblicazione su map-q-la28 (novità 1.4)
def gh_headers(accept="application/vnd.github+json"):
    """Intestazioni per l'API di GitHub (senza MAPPA_TOKEN si legge lo stesso: il repo è pubblico)."""
    h = {"Accept": accept, "X-GitHub-Api-Version": "2022-11-28"}
    if MAPPA_TOKEN:
        h["Authorization"] = f"Bearer {MAPPA_TOKEN}"
    return h


def leggi_json_pubblicato():
    """Il tennistavolo.json già pubblicato su map-q-la28: (sha, contenuto) oppure (None, None).
    Il file supera 1 MB: prima chiedo lo «sha» (serve per sovrascriverlo), poi il contenuto in versione
    «grezza» (raw), che l'API di GitHub dà fino a 100 MB (stesso sistema del badminton)."""
    if WTT_LOCALE:
        return None, None
    url = f"https://api.github.com/repos/{MAPPA_REPO}/contents/{FILE_WEB}"
    r = requests.get(url, headers=gh_headers(), timeout=30)
    if r.status_code == 404:
        return None, None
    if r.status_code != 200:
        raise RuntimeError(f"GitHub ha risposto {r.status_code}: {r.text[:300]}")
    sha = r.json().get("sha")
    r = requests.get(url, headers=gh_headers("application/vnd.github.raw+json"), timeout=90)
    if r.status_code != 200:
        raise RuntimeError(f"GitHub non dà il contenuto di {FILE_WEB}: {r.status_code}")
    try:
        return sha, json.loads(r.content.decode("utf-8"))
    except ValueError:
        return sha, None


def pubblica(payload):
    """Scrive tennistavolo.json su map-q-la28 e fa ripartire la pubblicazione del sito."""
    url = f"https://api.github.com/repos/{MAPPA_REPO}/contents/{FILE_WEB}"
    testo = json.dumps(payload, ensure_ascii=False, separators=(",", ":"))
    sha, vecchio = leggi_json_pubblicato()
    if vecchio and {**vecchio, "aggiornato": ""} == {**payload, "aggiornato": ""}:
        print("Pagina web: nessuna novità, non la ripubblico.")
        return
    corpo = {"message": "Aggiorna i risultati del tennistavolo",
             "content": base64.b64encode(testo.encode("utf-8")).decode("ascii")}
    if sha:
        corpo["sha"] = sha
    r = requests.put(url, headers=gh_headers(), json=corpo, timeout=180)
    if not r.ok:
        raise RuntimeError(f"GitHub non accetta {FILE_WEB}: {r.status_code} {r.text[:300]}")
    r = requests.post(f"https://api.github.com/repos/{MAPPA_REPO}/actions/workflows/{MAPPA_WORKFLOW}/dispatches",
                      headers=gh_headers(), json={"ref": "main"}, timeout=30)
    if r.status_code != 204:
        print(f"  Attenzione: {FILE_WEB} salvato, ma la ripubblicazione non è partita ({r.status_code}). "
              "Lancia a mano «Aggiorna mappa LA28» su map-q-la28.")
    else:
        print(f"Pagina web: {FILE_WEB} aggiornato ({len(testo) // 1024} KB), ripubblicazione avviata.")

# ------------------------------------------------------------------ programma principale
def main():
    oggi = date.today()
    print(f"Agente Tennis Tavolo {VERSIONE} · {datetime.now():%d/%m/%Y %H:%M} · "
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

    # 4. Tabelloni ufficiali (novità 1.4): dal sito WTT solo quelli che possono essere cambiati,
    #    gli altri dal tennistavolo.json già pubblicato; poi i gironi dalle righe di Notion
    try:
        _, pubblicato = leggi_json_pubblicato()
    except (RuntimeError, requests.RequestException) as e:
        pubblicato = None
        avviso(f"non riesco a rileggere {FILE_WEB} da GitHub ({e}): rileggo tutti i tabelloni")
    vecchi = (pubblicato or {}).get("tabelloni") or {}
    tabelloni = tabelloni_aggiornati(tornei, vecchi, oggi)
    aggiungi_gironi(tabelloni, righe_web)

    # 5. File per la pagina web: sempre negli Artifacts; nel lancio vero anche su map-q-la28
    payload = file_web(tornei, righe_web, oggi, tabelloni)
    with open(FILE_WEB, "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False, separators=(",", ":"))
    pubblicata = "no (prova)" if DRY_RUN else "no (manca MAPPA_TOKEN)"
    if not DRY_RUN and MAPPA_TOKEN:
        try:
            pubblica(payload)
            pubblicata = "sì"
        except (RuntimeError, requests.RequestException) as e:
            print(f"Pagina web non aggiornata: {e}")
            pubblicata = "NO, errore (vedi sopra)"
            errori += 1

    # 6. Riepilogo
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
    print(f"{FILE_WEB}: {len(payload['incontri'])} incontri, {len(payload['tornei'])} tornei, "
          f"{len(payload['tabelloni'])} tornei con tabellone · pubblicato su map-q-la28: {pubblicata}")
    if AVVISI:
        print(f"\nAvvisi ({len(AVVISI)}):")
        for a in AVVISI:
            print("  - " + a)
    print(f"Durata: {(time.time() - INIZIO) / 60:.1f} minuti")
    if errori:
        sys.exit(1)


if __name__ == "__main__":
    main()
