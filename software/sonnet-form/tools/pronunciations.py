#!/usr/bin/env python3
"""Deterministic, context-free pronunciation model, not historical reconstruction.

resolve(word) returns (ARPAbet phonemes, derivation) or None.  Dictionary
alternatives are resolved by their order in the frozen CMU dictionary, never
by their fit to meter or rhyme.  All spelling transformations affect lookup
tokens only: the Gutenberg text is never changed.
"""

from functools import lru_cache
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def tokenize(text):
    """Hyphens/dashes separate words; apostrophes may be contractions or quotes."""
    return re.findall(r"[’']?[A-Za-z]+(?:[’'][A-Za-z]+)*[’']?", text)


@lru_cache(maxsize=1)
def dictionary():
    entries = {}
    for line in (ROOT / "data/cmudict.dict").read_text(encoding="utf-8").splitlines():
        if not line or line.startswith(";;;"):
            continue
        word, *phones = line.split()
        word = re.sub(r"\(\d+\)$", "", word.lower())
        # CMU sometimes adds a comment after a pronunciation.
        if "#" in phones:
            phones = phones[:phones.index("#")]
        entries.setdefault(word, phones)
    return entries


@lru_cache(maxsize=1)
def overrides():
    return json.loads((ROOT / "data/pronunciation-overrides.json").read_text(encoding="utf-8"))


def suffix_s(phones):
    final = re.sub(r"\d", "", phones[-1])
    if final in {"S", "Z", "SH", "ZH", "CH", "JH"}:
        return phones + ["IH0", "Z"]
    return phones + (["S"] if final in {"P", "T", "K", "F", "TH"} else ["Z"])


def suffix_ed(phones):
    final = re.sub(r"\d", "", phones[-1])
    if final in {"T", "D"}:
        return phones + ["IH0", "D"]
    return phones + (["T"] if final in {"P", "K", "F", "TH", "S", "SH", "CH"} else ["D"])


def stems(word, suffix):
    stem = word[:-len(suffix)]
    options = [stem]
    if stem.endswith("i"):
        options.append(stem[:-1] + "y")
    options.append(stem + "e")
    if len(stem) > 2 and stem[-1] == stem[-2]:
        options.append(stem[:-1])
    return list(dict.fromkeys(options))


def resolve(word):
    normalized = word.lower().replace("’", "'").replace("‘", "'")
    answer = _resolve(normalized, 0)
    if answer is None:
        return None
    phones, derivation = answer
    prefix = "lowercase/curly-apostrophe normalization; " if normalized != word else ""
    return list(phones), prefix + derivation


@lru_cache(maxsize=None)
def _resolve(word, depth):
    if depth > 5 or not word:
        return None
    explicit = overrides().get(word)
    if explicit:
        return explicit["phonemes"], "explicit override: " + explicit["note"]
    if word in dictionary():
        return dictionary()[word], "CMU first pronunciation: " + word

    def attempt(candidate, description, transform=lambda p: p):
        if candidate == word:
            return None
        answer = _resolve(candidate, depth + 1)
        if answer:
            return transform(answer[0]), description + " -> " + answer[1]
        return None

    # Quote punctuation and plural possessive apostrophes have no segment.
    if word.endswith("'"):
        answer = attempt(word[:-1], "trailing quotation/plural possessive apostrophe")
        if answer:
            return answer
    if word.startswith("'"):
        answer = attempt(word[1:], "leading quotation apostrophe")
        if answer:
            return answer
    if word.endswith("'s"):
        answer = attempt(word[:-2], "possessive/contraction s allomorph", suffix_s)
        if answer:
            return answer
    if word.endswith("'d"):
        for candidate in [word[:-2] + "ed", word[:-2] + "d"]:
            answer = attempt(candidate, "written apostrophe-d expansion")
            if answer:
                return answer
    # Elided second-person suffix: consonantal st, no inserted syllable.
    if word.endswith("'st"):
        for candidate in [word[:-3], word[:-3] + "e"]:
            if candidate not in dictionary() and candidate not in overrides():
                continue
            answer = attempt(candidate, "written apostrophe-st suffix", lambda p: p + ["S", "T"])
            if answer:
                return answer
    # Full est/eth are syllabic in this deliberately literal lexical model.
    for suffix, phones in [("est", ["IH0", "S", "T"]), ("eth", ["IH0", "TH"])]:
        if word.endswith(suffix):
            for candidate in stems(word, suffix):
                if candidate not in dictionary() and candidate not in overrides():
                    continue
                answer = attempt(candidate, "syllabic archaic " + suffix, lambda p: p + phones)
                if answer:
                    return answer
    # UK spelling correspondence is lexical only, not a historical accent claim.
    candidates = []
    if "our" in word:
        candidates.append((word.replace("our", "or"), "British our/or spelling"))
    if "ll" in word:
        candidates.append((word.replace("ll", "l"), "British doubled-l spelling"))
    if "re" == word[-2:]:
        candidates.append((word[:-2] + "er", "British re/er spelling"))
    if "ise" in word:
        candidates.append((word.replace("ise", "ize"), "British ise/ize spelling"))
    if "isation" in word:
        candidates.append((word.replace("isation", "ization"), "British isation/ization spelling"))
    for candidate, description in candidates:
        # Restrict speculative spellings to direct dictionary entries.
        if candidate in dictionary():
            return dictionary()[candidate], description + " -> CMU first pronunciation: " + candidate
    # Regular inflection only when a stem is already recorded in CMU/overrides.
    for suffix, transform in [("ies", suffix_s), ("es", suffix_s), ("s", suffix_s),
                              ("ed", suffix_ed), ("ing", lambda p: p + ["IH0", "NG"])]:
        if not word.endswith(suffix):
            continue
        candidates = [word[:-3] + "y"] if suffix == "ies" else stems(word, suffix)
        for candidate in candidates:
            if candidate not in dictionary() and candidate not in overrides():
                continue
            answer = attempt(candidate, "regular " + suffix + " inflection", transform)
            if answer:
                return answer
    return None


def main():
    corpus = json.loads((ROOT / "data/sonnets.json").read_text(encoding="utf-8"))
    unknown = {}
    ending_unknown = {}
    for sonnet in corpus:
        for index, line in enumerate(sonnet["lines"], 1):
            words = tokenize(line)
            for word in words:
                if resolve(word) is None:
                    unknown.setdefault(word.lower().replace("’", "'"), []).append([sonnet["number"], index])
            if words and resolve(words[-1]) is None:
                ending_unknown.setdefault(words[-1].lower().replace("’", "'"), []).append([sonnet["number"], index])
    output = {"unresolved_tokens": unknown, "unresolved_line_endings": ending_unknown}
    (ROOT / "data/pronunciation-unknowns.json").write_text(json.dumps(output, ensure_ascii=False, indent=2) + "\n")
    print(f"Unknown tokens: {len(unknown)} types, {sum(map(len, unknown.values()))} occurrences")
    print(f"Unknown line endings: {len(ending_unknown)} types, {sum(map(len, ending_unknown.values()))} occurrences")
    print(json.dumps(output, ensure_ascii=False))


if __name__ == "__main__":
    main()
