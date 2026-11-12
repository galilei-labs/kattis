"""Rust source compaction, adapted from the extraction survey bundler.

Keep literals, token separation, and whole license/copyright comment groups.
This does not prune functions or rewrite extracted algorithms.
"""
import re


def without_runtime_tests(source):
    """Omit only the known trailing runtime test module; fail closed."""
    marker = re.search(r"(?m)^#\[cfg\(test\)\]\nmod tests \{\n", source)
    if marker is None:
        return source
    body, closing, suffix = source[marker.end():].rpartition("\n}")
    if not closing or suffix.strip() or any(line and not line[0].isspace()
                                          for line in body.splitlines()):
        raise ValueError("cannot safely omit runtime tests with unfamiliar layout")
    return source[:marker.start()]


def compact(source):
    notice = re.compile(r"license|copyright|spdx|©", re.I)
    char = re.compile(r"'(?:[^'\\\r\n]|\\(?:u\{[0-9a-fA-F_]+\}|x[0-9a-fA-F]{2}|[^\r\n]))'")
    raw_string = re.compile(r'(?:br|cr|r)(\#*)"')
    next_comment = re.compile(r"[ \t]*//")
    output = []
    i = 0
    while i < len(source):
        start = i
        if source.startswith("//", i):
            while True:
                end = source.find("\n", i)
                i = len(source) if end < 0 else end + 1
                following = next_comment.match(source, i)
                if not following:
                    break
                i = following.end() - 2
            text = source[start:i]
            output.append(text if notice.search(text) else " " + "\n" * text.count("\n"))
        elif source.startswith("/*", i):
            i += 2
            depth = 1
            while depth and i < len(source):
                if source.startswith("/*", i):
                    depth += 1
                    i += 2
                elif source.startswith("*/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError("unterminated Rust block comment")
            text = source[start:i]
            output.append(text if notice.search(text) else " " + "\n" * text.count("\n"))
        elif source[i].isspace():
            while i < len(source) and source[i].isspace():
                i += 1
            # Never fuse identifiers, literals, lifetimes or operator tokens.
            previous = output[-1][-1] if output and output[-1] else ""
            following = source[i:i + 1]
            delimiters = "(){}[],;"
            if previous and following and previous not in delimiters and following not in delimiters:
                output.append(" ")
        else:
            raw = raw_string.match(source, i)
            if raw:
                end_marker = '"' + raw[1]
                end = source.find(end_marker, raw.end())
                if end < 0:
                    raise ValueError("unterminated Rust raw string")
                i = end + len(end_marker)
            elif source[i] == '"':
                i += 1
                while i < len(source) and source[i] != '"':
                    i += 2 if source[i] == "\\" else 1
                if i >= len(source):
                    raise ValueError("unterminated Rust string")
                i += 1
            elif source[i] == "'" and (literal := char.match(source, i)):
                i = literal.end()
            else:
                i += 1
            output.append(source[start:i])
    return "".join(output)
