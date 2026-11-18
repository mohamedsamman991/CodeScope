"""

CodeScope — Python Project Intelligence Tool

============================================

- Deep scans Python projects (functions, classes, imports, conditions, loops)

- Obsidian-style graph with clear coloured orbs + hover tooltips

- Click any orb → deep AI explanation in plain English

- "Simplify" button → rewrites explanation in the simplest possible terms

- Optional AI provider settings; scanning and the graph work without AI



pip install -r requirements.txt

"""



import ast
import base64
import ctypes
import ctypes.wintypes
import http.client
from importlib import simple
import json
import os
import queue
import re
import socket
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass, field, replace
from datetime import datetime, timezone
from email.utils import parsedate_to_datetime
from pathlib import Path
from typing import Callable, Dict, Iterable, List, Optional, Tuple

import tkinter as tk
from tkinter import filedialog, messagebox, scrolledtext, ttk

import matplotlib
matplotlib.use("TkAgg")
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
import networkx as nx


PROVIDER_OPENAI = "OpenAI"
PROVIDER_GEMINI = "Google Gemini"
PROVIDER_ANTHROPIC = "Anthropic"
PROVIDER_GROQ = "Groq"
PROVIDER_OPENROUTER = "OpenRouter"
PROVIDER_COMPATIBLE = "OpenAI-compatible"
PROVIDER_OPENAI_COMPATIBLE = PROVIDER_COMPATIBLE
PROVIDERS = (
    
    PROVIDER_GEMINI,
   
)
_SUPPORTED_PROVIDERS = (
    *PROVIDERS,
    PROVIDER_COMPATIBLE,
)

OPENAI_BASE_URL = "https://api.openai.com/v1"
GEMINI_BASE_URL = "https://generativelanguage.googleapis.com/v1beta"
DEFAULT_GEMINI_MODEL = "gemini-3.1-flash-lite"
ANTHROPIC_BASE_URL = "https://api.anthropic.com"
GROQ_BASE_URL = "https://api.groq.com/openai/v1"
OPENROUTER_BASE_URL = "https://openrouter.ai/api/v1"
DEFAULT_BASE_URLS = {
    PROVIDER_OPENAI: OPENAI_BASE_URL,
    PROVIDER_GEMINI: GEMINI_BASE_URL,
    PROVIDER_ANTHROPIC: ANTHROPIC_BASE_URL,
    PROVIDER_GROQ: GROQ_BASE_URL,
    PROVIDER_OPENROUTER: OPENROUTER_BASE_URL,
}

SETTINGS_FILE = Path.home() / ".codescope_settings.json"
LEGACY_KEY_FILE = Path.home() / ".codescope_key"
_CREDENTIAL_PREFIX = "dpapi:"
_MAX_ERROR_DETAIL = 800


class _DataBlob(ctypes.Structure):
    _fields_ = [
        ("cbData", ctypes.wintypes.DWORD),
        ("pbData", ctypes.POINTER(ctypes.c_byte)),
    ]

@dataclass(frozen=True)
class ErrorResult:
    file: str
    line: int
    category: str
    source: str
    severity: str
    message: str


class ErrorAnalyzer:

    def analyze_file(self, file_path):
        source = Path(file_path).read_text(encoding="utf-8")

        try:
            ast.parse(source)

        except SyntaxError as error:
            line = error.lineno
            source_lines = source.splitlines()

            error_source = (
                source_lines[line - 1]
                if line and line <= len(source_lines)
                else ""
            )

            return ErrorResult(
                file=str(file_path),
                line=line or 0,
                category="SyntaxError",
                source=error_source,
                severity="Error",
                message=error.msg
            )

        return None

    def analyze_project(self, project_path):
        errors = []

        for file_path in Path(project_path).rglob("*.py"):
            try:
                result = self.analyze_file(file_path)
            except (OSError, UnicodeError):
                continue

            if result is not None:
                errors.append(result)

        return errors


@dataclass(frozen=True)
class AISettings:
    provider: str = PROVIDER_OPENAI
    api_key: str = ""
    model: str = ""
    base_url: str = ""
    credentials: Dict[str, str] = field(default_factory=dict)


class AIProviderError(Exception):
    """A provider failure with a sanitized, user-facing explanation."""

    def __init__(self, message: str, status: Optional[int] = None):
        super().__init__(message)
        self.status = status
        self.suggested_model: Optional[str] = None


def credential_storage_description() -> str:
    if os.name == "nt":
        return "API keys are protected with Windows DPAPI for your Windows account."
    return (
        "This platform has no configured OS credential backend; API keys are "
        "stored in the local settings file. Restrict access to your user account."
    )


def _protect_secret(value: str) -> str:
    if os.name != "nt":
        return value
    source = value.encode("utf-8")
    source_buffer = ctypes.create_string_buffer(source)
    source_blob = _DataBlob(
        len(source), ctypes.cast(source_buffer, ctypes.POINTER(ctypes.c_byte))
    )
    protected_blob = _DataBlob()
    if not ctypes.windll.crypt32.CryptProtectData(
        ctypes.byref(source_blob),
        "CodeScope API credential",
        None,
        None,
        None,
        0,
        ctypes.byref(protected_blob),
    ):
        raise OSError("Windows could not protect the API credential.")
    try:
        protected = ctypes.string_at(protected_blob.pbData, protected_blob.cbData)
        return _CREDENTIAL_PREFIX + base64.b64encode(protected).decode("ascii")
    finally:
        ctypes.windll.kernel32.LocalFree(protected_blob.pbData)


def _unprotect_secret(value: str) -> str:
    if not value.startswith(_CREDENTIAL_PREFIX):
        return value
    if os.name != "nt":
        raise ValueError(
            "Saved credentials were protected by Windows and cannot be opened here."
        )
    try:
        encrypted = base64.b64decode(value[len(_CREDENTIAL_PREFIX):], validate=True)
    except (ValueError, base64.binascii.Error):
        raise ValueError("A saved API credential could not be decoded.") from None
    encrypted_buffer = ctypes.create_string_buffer(encrypted)
    encrypted_blob = _DataBlob(
        len(encrypted),
        ctypes.cast(encrypted_buffer, ctypes.POINTER(ctypes.c_byte)),
    )
    plain_blob = _DataBlob()
    if not ctypes.windll.crypt32.CryptUnprotectData(
        ctypes.byref(encrypted_blob),
        None,
        None,
        None,
        None,
        0,
        ctypes.byref(plain_blob),
    ):
        raise ValueError(
            "Windows could not unlock a saved API credential for this account."
        )
    try:
        protected_text = ctypes.string_at(
            plain_blob.pbData, plain_blob.cbData
        ).decode("utf-8")
        return protected_text
    except UnicodeError:
        raise ValueError("A saved API credential is not valid text.") from None
    finally:
        ctypes.windll.kernel32.LocalFree(plain_blob.pbData)


def _clean_base_url(value: str) -> str:
    value = value.strip()
    if value.startswith("[") and "](" in value and value.endswith(")"):
        value = value[1:value.index("](")]
    return value.rstrip("/")


def _decode_saved_credentials(data: dict) -> Dict[str, str]:
    stored = data.get("credentials", {})
    if not isinstance(stored, dict):
        raise ValueError("Saved AI credentials have an invalid format.")
    credentials = {}
    for provider, secret in stored.items():
        if not isinstance(provider, str) or not isinstance(secret, str):
            raise ValueError("Saved AI credentials have an invalid format.")
        credentials[provider] = _unprotect_secret(secret)
    legacy_key = data.get("api_key", "")
    if not isinstance(legacy_key, str):
        raise ValueError("Saved AI credentials have an invalid format.")
    if legacy_key:
        credentials.setdefault(data.get("provider", PROVIDER_OPENAI), legacy_key)
    return credentials


def load_settings(
    settings_path: Path = SETTINGS_FILE,
    legacy_key_path: Path = LEGACY_KEY_FILE,
) -> AISettings:
    """Load saved provider settings, retaining support for the old Groq key file."""
    if settings_path.exists():
        try:
            data = json.loads(settings_path.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, OSError, UnicodeError):
            raise ValueError("Could not read saved AI settings. Open AI Settings to repair them.") from None
        if not isinstance(data, dict):
            raise ValueError("Saved AI settings have an invalid format.")
        provider = data.get("provider", PROVIDER_OPENAI)
        model = data.get("model", "")
        base_url = data.get("base_url", "")
        if provider not in _SUPPORTED_PROVIDERS:
            raise ValueError("Saved AI provider is not supported. Select one in AI Settings.")
        if not isinstance(model, str) or not isinstance(base_url, str):
            raise ValueError("Saved AI settings have an invalid format.")
        credentials = _decode_saved_credentials(data)
        if (
            provider == PROVIDER_GEMINI
            and model.removeprefix("models/") == "gemini-2.5-flash"
        ):
            model = DEFAULT_GEMINI_MODEL
        return AISettings(
            provider=provider,
            api_key=credentials.get(provider, ""),
            model=model,
            base_url=_clean_base_url(base_url),
            credentials=credentials,
        )

    legacy_key = ""
    try:
        if legacy_key_path.exists():
            legacy_key = legacy_key_path.read_text(encoding="utf-8").strip()
    except (OSError, UnicodeError):
        pass
    if not legacy_key:
        legacy_key = os.environ.get("GROQ_API_KEY", "").strip()
    if legacy_key:
        credentials = {PROVIDER_GROQ: legacy_key}
        return AISettings(
            provider=PROVIDER_GROQ,
            api_key=legacy_key,
            base_url=GROQ_BASE_URL,
            credentials=credentials,
        )
    return AISettings()


def save_settings(
    settings: AISettings,
    settings_path: Path = SETTINGS_FILE,
    clear_api_key: bool = False,
) -> bool:
    """Persist settings while retaining credentials for other providers."""
    credentials = dict(settings.credentials)
    is_default_path = settings_path.resolve() == SETTINGS_FILE.resolve()
    if settings_path.exists():
        try:
            existing_data = json.loads(settings_path.read_text(encoding="utf-8"))
            if isinstance(existing_data, dict):
                credentials = {
                    **_decode_saved_credentials(existing_data),
                    **credentials,
                }
        except (OSError, json.JSONDecodeError, ValueError):
            raise ValueError(
                "Existing AI settings could not be read safely; they were not overwritten."
            ) from None

    if settings.provider not in _SUPPORTED_PROVIDERS:
        raise ValueError("Select a supported AI provider before saving settings.")
    if clear_api_key:
        credentials.pop(settings.provider, None)
    else:
        api_key = settings.api_key.strip()
        if api_key:
            credentials[settings.provider] = api_key

    legacy_key = ""
    if is_default_path and LEGACY_KEY_FILE.exists():
        try:
            legacy_key = LEGACY_KEY_FILE.read_text(encoding="utf-8").strip()
        except (OSError, UnicodeError):
            raise ValueError(
                "The legacy Groq key could not be read; existing credentials were not changed."
            ) from None
        if legacy_key and not (
            clear_api_key and settings.provider == PROVIDER_GROQ
        ):
            credentials.setdefault(PROVIDER_GROQ, legacy_key)

    try:
        protected = {
            provider: _protect_secret(key)
            for provider, key in credentials.items()
            if key
        }
        payload = {
            "provider": settings.provider,
            "model": settings.model.strip(),
            "base_url": _clean_base_url(settings.base_url),
            "credentials": protected,
        }
        settings_path.parent.mkdir(parents=True, exist_ok=True)
        temporary_path = settings_path.with_suffix(settings_path.suffix + ".tmp")
        temporary_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
        if os.name != "nt":
            temporary_path.chmod(0o600)
        temporary_path.replace(settings_path)
        if os.name != "nt":
            settings_path.chmod(0o600)
    except (OSError, ValueError):
        raise ValueError("Could not save AI settings. Check access to your user profile.") from None
    if is_default_path and LEGACY_KEY_FILE.exists():
        try:
            LEGACY_KEY_FILE.unlink()
        except OSError:
            return True
    return False


def _default_base_url(provider: str) -> str:
    return DEFAULT_BASE_URLS.get(provider, "")


def infer_provider_from_api_key(api_key: str) -> Optional[str]:
    """Return a provider only when the key has a provider-specific prefix."""
    key = api_key.strip()
    if key.startswith("AIza"):
        return PROVIDER_GEMINI
    if key.startswith("gsk_"):
        return PROVIDER_GROQ
    if key.startswith("sk-ant-"):
        return PROVIDER_ANTHROPIC
    if key.startswith("sk-or-v1-"):
        return PROVIDER_OPENROUTER
    if key.startswith(("sk-proj-", "sk-svcacct-")):
        return PROVIDER_OPENAI
    return None


def _sanitize_detail(value: str, api_key: str) -> str:
    detail = value.replace(api_key, "[REDACTED]") if api_key else value
    detail = re.sub(r"(?i)bearer\s+\S+", "Bearer [REDACTED]", detail)
    detail = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]", " ", detail)
    return " ".join(detail.split())[:_MAX_ERROR_DETAIL]


def _api_error(
    status: int, detail: str, api_key: str, provider: Optional[str] = None
) -> AIProviderError:
    diagnostic = detail
    try:
        parsed = json.loads(detail)
        if isinstance(parsed, dict):
            provider_error = parsed.get("error", parsed)
            if isinstance(provider_error, dict):
                diagnostic = (
                    provider_error.get("message")
                    or provider_error.get("detail")
                    or provider_error.get("type")
                    or detail
                )
            elif isinstance(provider_error, str):
                diagnostic = provider_error
    except json.JSONDecodeError:
        pass
    clean_detail = _sanitize_detail(str(diagnostic), api_key)
    lowered = clean_detail.lower()
    if status == 401:
        summary = (
            "Google Gemini authentication failed. Verify that the API key is valid "
            "for the Gemini API."
            if provider == PROVIDER_GEMINI
            else "Authentication failed. Verify the API key for the selected provider."
        )
    elif status == 403:
        summary = (
            "Google Gemini denied access. Check API key restrictions, Gemini API "
            "enablement, and model availability."
            if provider == PROVIDER_GEMINI
            else "The provider denied access. Check account permissions and model access."
        )
    elif status == 404:
        if provider == PROVIDER_GEMINI:
            summary = (
                "Google Gemini could not find the model or API route. Confirm the "
                "model is available through the Gemini API."
            )
        else:
            summary = (
                "The provider could not find the model or API route. "
                "Verify the selected provider and model access."
            )
    elif status == 429:
        if "quota" in lowered or "billing" in lowered or "credit" in lowered:
            summary = "Provider quota or billing limit reached."
        else:
            summary = "Provider rate limit reached. Try again later."
    elif status == 400:
        summary = (
            "Google Gemini rejected the request. Check that the model supports "
            "content generation and that the request is valid."
            if provider == PROVIDER_GEMINI
            else "Provider rejected the request. Check the model ID and supported parameters."
        )
    elif status == 422:
        summary = "Provider rejected one or more request fields."
    elif status >= 500:
        summary = f"AI provider server error (HTTP {status})."
    else:
        summary = f"AI provider rejected the request (HTTP {status})."
    if clean_detail:
        return AIProviderError(
            f"{summary}\nProvider details: {clean_detail}", status=status
        )
    return AIProviderError(summary, status=status)


def _sse_events(response):
    event_name = ""
    data_lines = []
    for raw_line in response:
        line = raw_line.decode("utf-8", errors="replace").rstrip("\r\n")
        if not line:
            if data_lines:
                yield event_name, "\n".join(data_lines)
            event_name, data_lines = "", []
        elif line.startswith(":"):
            continue
        elif line.startswith("event:"):
            event_name = line[6:].strip()
        elif line.startswith("data:"):
            data_lines.append(line[5:].lstrip())
    if data_lines:
        yield event_name, "\n".join(data_lines)


def _text_content(content) -> str:
    if isinstance(content, str):
        return content
    if isinstance(content, list):
        return "".join(
            item.get("text", "")
            for item in content
            if isinstance(item, dict) and isinstance(item.get("text"), str)
        )
    return ""


_UNSUITABLE_MODEL_MARKERS = (
    "embedding", "embed-", "moderation", "whisper", "transcrib",
    "text-to-speech", "-tts", "dall-e", "gpt-image",
    "image-generation", "rerank", "classifier", "guard",
)

def _model_is_suitable(provider: str, model: dict) -> bool:
    model_id = model.get("id")
    if not isinstance(model_id, str) or not model_id.strip():
        return False
    lowered = model_id.lower()
    if any(marker in lowered for marker in _UNSUITABLE_MODEL_MARKERS):
        return False
    if provider == PROVIDER_OPENROUTER:
        architecture = model.get("architecture")
        if isinstance(architecture, dict):
            inputs = architecture.get("input_modalities")
            outputs = architecture.get("output_modalities")
            if isinstance(inputs, list) and "text" not in inputs:
                return False
            if isinstance(outputs, list) and "text" not in outputs:
                return False
    return True


def _model_rank(provider: str, model: dict) -> Tuple[float, float, str]:
    model_id = model["id"]
    lowered = model_id.lower()
    if provider == PROVIDER_GEMINI and lowered == DEFAULT_GEMINI_MODEL:
        return (-1, 0, lowered)
    if provider == PROVIDER_OPENROUTER:
        pricing = model.get("pricing")
        if isinstance(pricing, dict):
            try:
                cost = float(pricing.get("prompt", "inf")) + float(
                    pricing.get("completion", "inf")
                )
            except (TypeError, ValueError):
                cost = float("inf")
            return (0 if lowered.endswith(":free") else 1, cost, lowered)
        if lowered.endswith(":free"):
            return (0, 0.0, lowered)
    efficient = any(
        marker in lowered
        for marker in ("mini", "flash-lite", "haiku", "instant", "8b", ":free")
    )
    capable = efficient or any(marker in lowered for marker in ("flash", "lite"))
    preview = any(marker in lowered for marker in ("preview", "experimental", "beta"))
    return (0 if efficient else 1 if capable else 2, 1 if preview else 0, lowered)


def select_model(provider: str, models: Iterable[str]) -> str:
    """Select a preferred text-generation model from discovered model IDs."""
    suitable = [
        model.strip()
        for model in models
        if isinstance(model, str)
        and model.strip()
        and not any(marker in model.lower() for marker in _UNSUITABLE_MODEL_MARKERS)
    ]
    if not suitable:
        raise AIProviderError(
            f"No text-generation models are available for {provider}. "
            "Check the API key, account access, and provider model availability."
        )
    return min(
        dict.fromkeys(suitable),
        key=lambda model: _model_rank(provider, {"id": model}),
    )


def _ranked_model_ids(provider: str, entries: list) -> List[str]:
    if not isinstance(entries, list):
        raise AIProviderError("Provider returned malformed model-list data.")
    suitable = [
        item for item in entries
        if isinstance(item, dict) and _model_is_suitable(provider, item)
    ]
    return [
        item["id"]
        for item in sorted(suitable, key=lambda item: _model_rank(provider, item))
    ]


def _with_query(url: str, params: dict) -> str:
    parsed = urllib.parse.urlsplit(url)
    query = urllib.parse.parse_qsl(parsed.query, keep_blank_values=True)
    query.extend(params.items())
    return urllib.parse.urlunsplit(
        (parsed.scheme, parsed.netloc, parsed.path, urllib.parse.urlencode(query), parsed.fragment)
    )


class ProviderAdapter:
    def __init__(self, settings: AISettings):
        self.settings = settings
        self.api_key = settings.api_key.strip()
        self.model = settings.model.strip()
        self.base_url = _clean_base_url(
            settings.base_url or _default_base_url(settings.provider)
        )

    def _validate(self, require_model: bool = True):
        if require_model and not self.model:
            raise AIProviderError(
                "No model is selected. Test the connection to discover an available model."
            )
        if not self.base_url:
            raise AIProviderError("Enter a provider base URL in AI Settings.")
        try:
            parsed = urllib.parse.urlsplit(self.base_url)
        except ValueError:
            raise AIProviderError("Enter a valid HTTP or HTTPS base URL.") from None
        if (
            parsed.scheme not in ("http", "https")
            or not parsed.netloc
            or not parsed.hostname
            or parsed.username
            or parsed.password
            or parsed.query
            or parsed.fragment
        ):
            raise AIProviderError(
                "Base URL must be HTTP or HTTPS without credentials, query, or fragment."
            )
        try:
            port = parsed.port
        except ValueError:
            raise AIProviderError("Enter a valid HTTP or HTTPS base URL.") from None
        if port is not None and not 1 <= port <= 65535:
            raise AIProviderError("Enter a valid HTTP or HTTPS base URL.")
        if parsed.scheme == "http" and parsed.hostname.lower() not in {
            "localhost",
            "127.0.0.1",
            "::1",
        }:
            raise AIProviderError(
                "Use HTTPS for remote API base URLs. Plain HTTP is allowed only on loopback."
            )
        if not self.api_key and parsed.hostname.lower() not in {
            "localhost",
            "127.0.0.1",
            "::1",
        }:
            raise AIProviderError("Add an API key in AI Settings before using AI.")

    def _url(self, path: str) -> str:
        self._validate(require_model=False)
        if not path:
            return self.base_url
        return self.base_url + "/" + path.lstrip("/")

    def _headers(self) -> Dict[str, str]:
        if not self.api_key:
            return {}
        return {"Authorization": f"Bearer {self.api_key}"}

    def build_request(self, messages, max_tokens: int):
        raise NotImplementedError

    def parse_stream(self, response, on_chunk, cancel_event) -> Tuple[bool, bool]:
        raise NotImplementedError

    def _emit(self, text, on_chunk):
        if text:
            on_chunk(text)
            return True
        return False

    def _request_error(self, event, data):
        try:
            parsed = json.loads(data)
        except json.JSONDecodeError:
            parsed = {}
        error = parsed.get("error", parsed) if isinstance(parsed, dict) else {}
        if isinstance(error, dict):
            detail = error.get("message") or error.get("detail") or ""
        else:
            detail = str(error)
        raise AIProviderError(
            f"Provider streaming error: {_sanitize_detail(str(detail), self.api_key)}"
        )

    def discover_models(self) -> List[str]:
        raise AIProviderError("Model discovery is not available for this provider; enter a model ID.")


class OpenAICompatibleAdapter(ProviderAdapter):
    def _endpoint(self, path: str) -> str:
        base = self._url("")
        if path == "chat/completions" and base.endswith("/chat/completions"):
            return base
        return base + "/" + path.lstrip("/")

    def build_request(self, messages, max_tokens: int):
        token_name = "max_completion_tokens"
        if self.settings.provider in (PROVIDER_GROQ, PROVIDER_COMPATIBLE):
            token_name = (
                "max_completion_tokens"
                if "gpt-oss" in self.model.lower()
                else "max_tokens"
            )
        body = {
            "model": self.model,
            "messages": list(messages),
            "stream": True,
            token_name: max_tokens,
        }
        return urllib.request.Request(
            self._endpoint("chat/completions"),
            data=json.dumps(body).encode("utf-8"),
            headers={
                **self._headers(),
                "Content-Type": "application/json",
                "Accept": "text/event-stream",
                "User-Agent": "CodeScope/1.0",
            },
            method="POST",
        )

    def parse_stream(self, response, on_chunk, cancel_event):
        has_content = False
        cancelled = False
        for _, data in _sse_events(response):
            if cancel_event and cancel_event.is_set():
                cancelled = True
                break
            if data == "[DONE]":
                break
            try:
                event = json.loads(data)
            except json.JSONDecodeError:
                raise AIProviderError("Provider returned malformed streaming data.") from None
            if not isinstance(event, dict):
                continue
            if event.get("error"):
                self._request_error("", data)
            choices = event.get("choices")
            if not isinstance(choices, list) or not choices or not isinstance(choices[0], dict):
                continue
            delta = choices[0].get("delta")
            if not isinstance(delta, dict):
                continue
            content = delta.get("content")
            text = _text_content(content)
            refusal = delta.get("refusal")
            if isinstance(refusal, str):
                text += refusal
            has_content |= self._emit(text, on_chunk)
        return has_content, cancelled

    def _models_url(self):
        base = self._url("")
        if base.endswith("/chat/completions"):
            base = base[: -len("/chat/completions")]
        return base + "/models"

    def _models_headers(self):
        return self._headers()

    def discover_models(self):
        self._validate(require_model=False)
        models = []
        url = self._models_url()
        for _ in range(10):
            request = urllib.request.Request(
                url, headers=self._models_headers(), method="GET"
            )
            data = _get_json(request, self.api_key, self.settings.provider)
            page = data.get("data")
            if not isinstance(page, list):
                raise AIProviderError("Provider returned malformed model-list data.")
            models.extend(page)
            if not data.get("has_more"):
                break
            cursor = data.get("last_id")
            if not isinstance(cursor, str) or not cursor:
                raise AIProviderError(
                    "Provider returned incomplete model-list pagination data."
                )
            url = _with_query(self._models_url(), {"after": cursor, "limit": "100"})
        else:
            raise AIProviderError(
                "Provider model list exceeded the supported pagination limit."
            )
        return _ranked_model_ids(self.settings.provider, models)


class OpenAIAdapter(OpenAICompatibleAdapter):
    pass


class GroqAdapter(OpenAICompatibleAdapter):
    pass


class OpenRouterAdapter(OpenAICompatibleAdapter):
    pass


class CompatibleAdapter(OpenAICompatibleAdapter):
    pass


class AnthropicAdapter(ProviderAdapter):
    def _headers(self):
        if not self.api_key:
            return {}
        return {
            "x-api-key": self.api_key,
            "anthropic-version": "2023-06-01",
        }

    def build_request(self, messages, max_tokens: int):
        system = []
        content_messages = []
        for message in messages:
            if message.get("role") == "system":
                system.append(message.get("content", ""))
            else:
                content_messages.append(
                    {"role": message.get("role", "user"), "content": message.get("content", "")}
                )
        body = {
            "model": self.model,
            "max_tokens": max_tokens,
            "stream": True,
            "messages": content_messages,
        }
        if system:
            body["system"] = "\n\n".join(system)
        return urllib.request.Request(
            self._url("v1/messages"),
            data=json.dumps(body).encode("utf-8"),
            headers={
                **self._headers(),
                "Content-Type": "application/json",
                "Accept": "text/event-stream",
            },
            method="POST",
        )

    def parse_stream(self, response, on_chunk, cancel_event):
        has_content = False
        cancelled = False
        for event_name, data in _sse_events(response):
            if cancel_event and cancel_event.is_set():
                cancelled = True
                break
            if data == "[DONE]":
                break
            try:
                event = json.loads(data)
            except json.JSONDecodeError:
                raise AIProviderError("Anthropic returned malformed streaming data.") from None
            if not isinstance(event, dict):
                continue
            if event_name == "error" or event.get("type") == "error":
                self._request_error(event_name, data)
            if event.get("type") != "content_block_delta":
                continue
            delta = event.get("delta")
            if isinstance(delta, dict):
                has_content |= self._emit(delta.get("text", ""), on_chunk)
        return has_content, cancelled

    def discover_models(self):
        self._validate(require_model=False)
        models = []
        url = self._url("v1/models")
        for _ in range(10):
            request = urllib.request.Request(
                url,
                headers={**self._headers(), "anthropic-version": "2023-06-01"},
                method="GET",
            )
            data = _get_json(request, self.api_key, self.settings.provider)
            page = data.get("data")
            if not isinstance(page, list):
                raise AIProviderError("Anthropic returned malformed model-list data.")
            models.extend(page)
            if not data.get("has_more"):
                break
            cursor = data.get("last_id")
            if not isinstance(cursor, str) or not cursor:
                raise AIProviderError(
                    "Anthropic returned incomplete model-list pagination data."
                )
            url = _with_query(self._url("v1/models"), {"after_id": cursor, "limit": "100"})
        else:
            raise AIProviderError(
                "Anthropic model list exceeded the supported pagination limit."
            )
        return _ranked_model_ids(self.settings.provider, models)


class GeminiAdapter(ProviderAdapter):
    def _headers(self):
        if not self.api_key:
            return {}
        return {"x-goog-api-key": self.api_key}

    def build_request(self, messages, max_tokens: int):
        system = []
        contents = []
        for message in messages:
            role = message.get("role", "user")
            if role == "system":
                system.append(message.get("content", ""))
            else:
                contents.append(
                    {
                        "role": "model" if role == "assistant" else "user",
                        "parts": [{"text": message.get("content", "")}],
                    }
                )
        body = {
            "contents": contents,
            "generationConfig": {"maxOutputTokens": max_tokens},
        }
        if system:
            body["systemInstruction"] = {"parts": [{"text": "\n\n".join(system)}]}
        model = self.model.removeprefix("models/")
        endpoint = self._url(
            f"models/{urllib.parse.quote(model, safe='')}:streamGenerateContent?alt=sse"
        )
        return urllib.request.Request(
            endpoint,
            data=json.dumps(body).encode("utf-8"),
            headers={**self._headers(), "Content-Type": "application/json", "Accept": "text/event-stream"},
            method="POST",
        )

    def parse_stream(self, response, on_chunk, cancel_event):
        has_content = False
        cancelled = False
        for _, data in _sse_events(response):
            if cancel_event and cancel_event.is_set():
                cancelled = True
                break
            try:
                event = json.loads(data)
            except json.JSONDecodeError:
                raise AIProviderError("Google Gemini returned malformed streaming data.") from None
            if not isinstance(event, dict):
                continue
            if event.get("error"):
                self._request_error("", data)
            candidates = event.get("candidates")
            if not isinstance(candidates, list) or not candidates:
                feedback = event.get("promptFeedback", {})
                if isinstance(feedback, dict) and feedback.get("blockReason"):
                    has_content |= self._emit(
                        f"Request blocked: {feedback['blockReason']}.", on_chunk
                    )
                continue
            candidate = candidates[0]
            content = candidate.get("content", {}) if isinstance(candidate, dict) else {}
            parts = content.get("parts", []) if isinstance(content, dict) else []
            text = "".join(
                part.get("text", "")
                for part in parts
                if isinstance(part, dict)
                and isinstance(part.get("text"), str)
                and not part.get("thought", False)
            )
            if not text and isinstance(candidate, dict):
                if candidate.get("finishReason") in ("SAFETY", "BLOCKLIST", "PROHIBITED_CONTENT"):
                    text = "Request blocked by the model's safety policy."
            has_content |= self._emit(text, on_chunk)
        return has_content, cancelled

    def _models_url(self):
        return self._url("models")

    def discover_models(self):
        self._validate(require_model=False)
        models = []
        url = self._models_url()
        for _ in range(10):
            request = urllib.request.Request(url, headers=self._headers(), method="GET")
            data = _get_json(request, self.api_key, self.settings.provider)
            page = data.get("models")
            if not isinstance(page, list):
                raise AIProviderError(
                    "Google Gemini returned malformed model-list data."
                )
            for item in page:
                methods = item.get("supportedGenerationMethods", []) if isinstance(item, dict) else []
                name = item.get("name", "") if isinstance(item, dict) else ""
                name_tokens = (
                    re.split(r"[-_/]", name.lower())
                    if isinstance(name, str)
                    else []
                )
                if (
                    isinstance(item, dict)
                    and isinstance(methods, list)
                    and "generateContent" in methods
                    and isinstance(name, str)
                    and not {"image", "imagegen", "imagegeneration", "imagen"}.intersection(
                        name_tokens
                    )
                ):
                    models.append(
                        {**item, "id": name.removeprefix("models/")}
                    )
            page_token = data.get("nextPageToken")
            if not page_token:
                break
            if not isinstance(page_token, str):
                raise AIProviderError(
                    "Google Gemini returned invalid model-list pagination data."
                )
            url = _with_query(
                self._models_url(),
                {"pageToken": page_token, "pageSize": "1000"},
            )
        else:
            raise AIProviderError(
                "Google Gemini model list exceeded the supported pagination limit."
            )
        return _ranked_model_ids(self.settings.provider, models)



def _get_json(request, api_key: str, provider: Optional[str] = None):
    try:
        with urllib.request.urlopen(request, timeout=30) as response:
            data = json.loads(response.read().decode("utf-8"))
    except urllib.error.HTTPError as error:
        try:
            detail = error.read().decode("utf-8", errors="replace")
        finally:
            error.close()
        raise _api_error(error.code, detail, api_key, provider) from None
    except (
        urllib.error.URLError,
        http.client.HTTPException,
        TimeoutError,
        socket.timeout,
        OSError,
    ):
        raise AIProviderError(
            "Could not reach the provider model list. "
            "Check your internet connection and provider status."
        ) from None
    except (json.JSONDecodeError, UnicodeDecodeError):
        raise AIProviderError(
            "Provider returned malformed model-list data."
        ) from None

    if not isinstance(data, dict):
        raise AIProviderError(
            "Provider returned an unsupported model-list response."
        )
    return data


_ADAPTERS = {
    PROVIDER_GEMINI: GeminiAdapter,
}



class ChatCompletionsClient:
    """Stable facade for provider-specific chat APIs and SSE streams."""

    def __init__(
        self,
        settings: AISettings,
        timeout: float = 90.0,
        retries: int = 3,
        sleep_fn: Callable[[float], None] = time.sleep,
    ):
        self.settings = settings
        self.timeout = timeout
        self.retries = max(0, retries)
        self.sleep_fn = sleep_fn
        self.selected_model = settings.model.strip()
        try:
            adapter_type = _ADAPTERS[settings.provider]
        except KeyError:
            raise AIProviderError("Select a supported AI provider in AI Settings.") from None
        self.adapter = adapter_type(settings)

    def _ensure_model(self):
        if self.adapter.model:
            return
        models = self.discover_models()
        model = models[0] if models else select_model(self.settings.provider, models)
        self.selected_model = model
        self.settings = replace(self.settings, model=model)
        self.adapter.settings = self.settings
        self.adapter.model = model

    def _suggest_alternative(self, error: AIProviderError):
        if error.status not in (403, 404):
            return
        try:
            alternatives = [
                model for model in self.discover_models()
                if model != self.adapter.model
            ]
            if not alternatives:
                return
            suggestion = alternatives[0]
        except AIProviderError:
            return
        error.suggested_model = suggestion
        error.args = (
            f"{error}\nAnother discovered model is available: {suggestion}. "
            "Try it from AI Settings.",
        )


    def stream_chat(
        self,
        messages: Iterable[Dict[str, str]],
        on_chunk: Callable[[str], None],
        max_tokens: int = 1000,
        cancel_event=None,
    ) -> bool:
        """Stream one completion. Retries happen only before response streaming begins."""

        if max_tokens < 1:
            raise AIProviderError("Token limit must be at least 1.")

        adapter = self.adapter
        self._ensure_model()
        adapter._validate()

        request = adapter.build_request(messages, max_tokens)

        for attempt in range(self.retries + 1):

            if cancel_event and cancel_event.is_set():
                return False

            # STEP 1: Open the connection
            try:
                response = urllib.request.urlopen(
                    request,
                    timeout=self.timeout
                )

            except urllib.error.HTTPError as error:
                status = error.code
                retry_after = error.headers.get("Retry-After")

                try:
                    detail = error.read().decode(
                        "utf-8",
                        errors="replace"
                    )
                finally:
                    error.close()

                retryable = status in (500, 502, 503, 504) or (
                    status == 429 and _rate_limit_is_transient(detail)
                )

                if retryable and attempt < self.retries:
                    self.sleep_fn(_retry_delay(attempt, retry_after))
                    continue

                print(f"[DEBUG] Chat HTTP status: {status}")

                provider_error = _api_error(
                    status,
                    detail,
                    adapter.api_key,
                    self.settings.provider
                )

                self._suggest_alternative(provider_error)
                raise provider_error from None

            except (
                urllib.error.URLError,
                TimeoutError,
                socket.timeout,
                OSError,
            ) as error:

                print(
                    f"[DEBUG] Connection error: "
                    f"{type(error).__name__}: {error}"
                )

                if attempt < self.retries:
                    self.sleep_fn(_retry_delay(attempt, None))
                    continue

                raise AIProviderError(
                    f"Connection failed: {type(error).__name__}: {error}"
                ) from error

            except http.client.HTTPException:

                if attempt < self.retries:
                    self.sleep_fn(_retry_delay(attempt, None))
                    continue

                raise AIProviderError(
                    "The AI connection failed before streaming began."
                ) from None

            # STEP 2: Read the response stream
            try:
                with response:
                    has_content, cancelled = adapter.parse_stream(
                        response,
                        on_chunk,
                        cancel_event
                    )

            except AIProviderError:
                raise

            except (
                urllib.error.URLError,
                http.client.HTTPException,
                TimeoutError,
                socket.timeout,
                OSError,
            ):
                raise AIProviderError(
                    "The response stream was interrupted. "
                    "Partial output was kept; retry manually."
                ) from None

            # STEP 3: Check the result
            if cancelled:
                return False

            if not has_content:
                raise AIProviderError(
                    "The provider returned no text. The model may have refused "
                    "the request or returned only reasoning. "
                    "Check the model and try again."
                )

            return True

        raise AIProviderError(
            "The AI request could not be completed."
        )

    def discover_models(self) -> List[str]:
        return self.adapter.discover_models()

    def stream(self, messages, on_chunk, max_tokens=1000, cancel_event=None):
        return self.stream_chat(
            messages,
            on_chunk,
            max_tokens=max_tokens,
            cancel_event=cancel_event,
        )


def _retry_delay(attempt: int, retry_after: Optional[str]) -> float:
    if retry_after:
        try:
            return min(max(float(retry_after), 0.0), 10.0)
        except ValueError:
            try:
                retry_at = parsedate_to_datetime(retry_after)
                if retry_at.tzinfo is None:
                    retry_at = retry_at.replace(tzinfo=timezone.utc)
                return min(max((retry_at - datetime.now(timezone.utc)).total_seconds(), 0.0), 10.0)
            except (TypeError, ValueError, OverflowError):
                pass
    return min(0.5 * (2 ** attempt), 5.0)


def _rate_limit_is_transient(detail: str) -> bool:
    try:
        parsed = json.loads(detail)
        error = parsed.get("error", parsed) if isinstance(parsed, dict) else {}
        if isinstance(error, dict):
            detail = str(error.get("message") or error.get("code") or detail)
    except json.JSONDecodeError:
        pass
    lowered = detail.lower()
    return not any(term in lowered for term in ("quota", "billing", "credit", "insufficient_quota"))


# ── Colours ───────────────────────────────────────────────────────────────────

C = {

    "bg":        "#0d0d1a",

    "panel":     "#13132b",

    "border":    "#1e1e3f",

    "text":      "#e8e8ff",

    "dim":       "#5a5a8a",

    "file":      "#a855f7",   # bright purple  — file

    "function":  "#22d3ee",   # bright cyan    — function

    "class":     "#fbbf24",   # bright amber   — class

    "import":    "#34d399",   # bright green   — imports

    "condition": "#fb7185",   # bright pink    — if/try

    "loop":      "#818cf8",   # bright indigo  — for/while

    "selected":  "#ffffff",

    "edge":      "#2a2a4a",

    "edge_sel":  "#a855f7",

    "simplify":  "#0ea5e9",   # sky blue — simplify button

}



SKIP = {".venv","venv","__pycache__",".git","node_modules",
        "dist","build",".eggs",".tox","site-packages",".mypy_cache"}

# ── Deep Scanner ──────────────────────────────────────────────────────────────



def scan_project(root: str) -> dict:

    root_path = Path(root).resolve()

    py_files  = [f for f in root_path.rglob("*.py")

                 if not any(s in f.parts for s in SKIP)]



    module_map = {}

    for f in py_files:

        rel = f.relative_to(root_path)

        module_map[".".join(rel.with_suffix("").parts)] = str(rel)



    files, edges = {}, []

    for f in py_files:

        rel = str(f.relative_to(root_path))

        try:

            src  = f.read_text(encoding="utf-8", errors="ignore")

            info = deep_parse(src, rel)

            info["source"] = src

            files[rel] = info

            for imp in info["imports"]:

                for mod, mp in module_map.items():

                    if imp == mod or imp.startswith(mod+"."):

                        if mp != rel:

                            edges.append({"source": rel, "target": mp})

                        break

        except Exception as e:

            files[rel] = {"path":rel,"error":str(e),"imports":[],"functions":[],

                          "classes":[],"conditions":0,"loops":0,"source":"","line_count":0}



    return {"files": files, "edges": edges, "root": str(root_path)}





def deep_parse(src: str, path: str) -> dict:

    try:

        tree = ast.parse(src)

    except SyntaxError as e:

        return {"path":path,"imports":[],"functions":[],"classes":[],

                "conditions":0,"loops":0,"line_count":src.count("\n")+1,

                "parse_error":str(e)}



    imports, functions, classes = [], [], []

    conditions = loops = 0



    for node in ast.walk(tree):

        if isinstance(node, ast.Import):

            for a in node.names: imports.append(a.name)

        elif isinstance(node, ast.ImportFrom):

            if node.module: imports.append(node.module)

        elif isinstance(node, (ast.If, ast.Try, ast.ExceptHandler)):

            conditions += 1

        elif isinstance(node, (ast.For, ast.While, ast.comprehension)):

            loops += 1



    for node in ast.iter_child_nodes(tree):

        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):

            fn_conds = sum(1 for n in ast.walk(node) if isinstance(n,(ast.If,ast.Try)))

            fn_loops = sum(1 for n in ast.walk(node) if isinstance(n,(ast.For,ast.While)))

            functions.append({

                "name":      node.name,

                "line":      node.lineno,

                "args":      [a.arg for a in node.args.args],

                "docstring": ast.get_docstring(node),

                "is_async":  isinstance(node, ast.AsyncFunctionDef),

                "conditions":fn_conds,

                "loops":     fn_loops,

                "source":    ast.get_source_segment(src, node) or "",

            })

        elif isinstance(node, ast.ClassDef):

            methods = []

            for m in node.body:

                if isinstance(m,(ast.FunctionDef,ast.AsyncFunctionDef)):

                    methods.append({

                        "name":      m.name,

                        "args":      [a.arg for a in m.args.args if a.arg!="self"],

                        "source":    ast.get_source_segment(src, m) or "",

                        "docstring": ast.get_docstring(m),

                    })

            classes.append({

                "name":      node.name,

                "line":      node.lineno,

                "methods":   methods,

                "docstring": ast.get_docstring(node),

                "source":    ast.get_source_segment(src, node) or "",

            })



    return {

        "path":       path,

        "imports":    list(set(imports)),

        "functions":  functions,

        "classes":    classes,

        "conditions": conditions,

        "loops":      loops,

        "line_count": src.count("\n")+1,

        "docstring":  ast.get_docstring(tree),

    }





# ── Graph ─────────────────────────────────────────────────────────────────────



class CodeGraph:

    def __init__(self, frame, on_select_cb):

        self.on_select  = on_select_cb

        self.selected   = None

        self.G          = nx.DiGraph()

        self.pos        = {}

        self.node_meta  = {}

        self._ann       = None

        self._pan_start = self._xlim = self._ylim = None



        self.fig, self.ax = plt.subplots(figsize=(9,7), facecolor=C["bg"])

        self.ax.set_facecolor(C["bg"])

        self.ax.axis("off")

        self.fig.tight_layout(pad=0)



        self.canvas = FigureCanvasTkAgg(self.fig, master=frame)

        self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)



        self.canvas.mpl_connect("button_press_event",  self._click)

        self.canvas.mpl_connect("scroll_event",        self._scroll)

        self.canvas.mpl_connect("motion_notify_event", self._hover)

        self.canvas.mpl_connect("button_press_event",  self._pan_press)

        self.canvas.mpl_connect("motion_notify_event", self._pan_move)

        self.canvas.mpl_connect("button_release_event",self._pan_release)



    def load(self, scan: dict):

        self.G.clear()

        self.node_meta.clear()

        files = scan["files"]



        for rel, info in files.items():

            nid = f"file::{rel}"

            self.G.add_node(nid)

            self.node_meta[nid] = {"type":"file","label":Path(rel).name,

                                   "data":info,"rel":rel}



        for rel, info in files.items():

            fnid = f"file::{rel}"

            for fn in info.get("functions",[]):

                nid = f"func::{rel}::{fn['name']}"

                self.G.add_node(nid)

                self.G.add_edge(fnid, nid)

                self.node_meta[nid] = {"type":"function","label":fn["name"]+"()",

                                       "data":fn,"rel":rel}

            for cl in info.get("classes",[]):

                nid = f"class::{rel}::{cl['name']}"

                self.G.add_node(nid)

                self.G.add_edge(fnid, nid)

                self.node_meta[nid] = {"type":"class","label":cl["name"],

                                       "data":cl,"rel":rel}

            if info.get("imports"):

                nid = f"imports::{rel}"

                self.G.add_node(nid)

                self.G.add_edge(fnid, nid)

                self.node_meta[nid] = {"type":"import",

                                       "label":f"imports ({len(info['imports'])})",

                                       "data":info["imports"],"rel":rel}

            if info.get("conditions",0) > 0:

                nid = f"cond::{rel}"

                self.G.add_node(nid)

                self.G.add_edge(fnid, nid)

                self.node_meta[nid] = {"type":"condition",

                                       "label":f"{info['conditions']} conditions",

                                       "data":info,"rel":rel}

            if info.get("loops",0) > 0:

                nid = f"loop::{rel}"

                self.G.add_node(nid)

                self.G.add_edge(fnid, nid)

                self.node_meta[nid] = {"type":"loop",

                                       "label":f"{info['loops']} loops",

                                       "data":info,"rel":rel}



        for edge in scan["edges"]:

            s, t = f"file::{edge['source']}", f"file::{edge['target']}"

            if s in self.G and t in self.G:

                self.G.add_edge(s, t)



        k = 3.5 / (len(self.G.nodes)**0.5 + 0.1)

        self.pos = nx.spring_layout(self.G, k=k, iterations=100, seed=42)

        self.draw()



    def draw(self):

        self.ax.clear()

        self.ax.set_facecolor(C["bg"])

        self.ax.axis("off")

        self._ann = None



        if not self.G.nodes:

            self.ax.text(0.5, 0.5, "Open a Python project to start.",

                         ha="center", va="center", color=C["dim"],

                         fontsize=14, transform=self.ax.transAxes)

            self.canvas.draw()

            return



        # Node visuals

        node_colors, node_sizes, edge_widths = [], [], []

        for nid in self.G.nodes:

            meta  = self.node_meta.get(nid, {})

            ntype = meta.get("type","file")

            is_sel = nid == self.selected

            color = C["selected"] if is_sel else C.get(ntype, C["file"])

            # bigger orbs for files, medium for classes/functions, small for rest

            if ntype == "file":       size = 900

            elif ntype in ("class","function"): size = 500

            else:                     size = 280

            if is_sel: size = int(size * 1.4)

            node_colors.append(color)

            node_sizes.append(size)



        edge_colors = [

            C["edge_sel"] if self.selected in (u,v) else C["edge"]

            for u,v in self.G.edges

        ]



        # Draw glow effect for selected node

        if self.selected and self.selected in self.pos:

            sx, sy = self.pos[self.selected]

            meta   = self.node_meta.get(self.selected, {})

            ntype  = meta.get("type","file")

            glow_c = C.get(ntype, C["file"])

            for alpha, mult in [(0.08,4.0),(0.15,2.5),(0.25,1.8)]:

                self.ax.scatter([sx],[sy],

                                s=node_sizes[list(self.G.nodes).index(self.selected)]*mult,

                                c=glow_c, alpha=alpha, zorder=1)



        nx.draw_networkx_edges(self.G, self.pos, ax=self.ax,

                               edge_color=edge_colors, arrows=True,

                               arrowstyle="-|>", arrowsize=14,

                               width=1.2, alpha=0.5, min_source_margin=15,

                               min_target_margin=15)



        nx.draw_networkx_nodes(self.G, self.pos, ax=self.ax,

                               node_color=node_colors, node_size=node_sizes,

                               alpha=0.95, linewidths=2,

                               edgecolors=[C.get(self.node_meta.get(n,{}).get("type","file"), C["file"])

                                           for n in self.G.nodes])



        # Labels

        for nid, (x, y) in self.pos.items():

            meta  = self.node_meta.get(nid,{})

            label = meta.get("label", nid)

            is_sel = nid == self.selected

            fsize = 8 if meta.get("type") == "file" else 6.5

            fw    = "bold" if is_sel else "normal"

            color = C["selected"] if is_sel else C["text"]

            short = label if len(label) <= 16 else label[:14]+"…"

            self.ax.text(x, y-0.065, short, ha="center", va="top",

                         fontsize=fsize, fontweight=fw,

                         color=color, fontfamily="monospace", clip_on=True)



        # Legend

        legend = [

            mpatches.Patch(color=C["file"],      label="● File"),

            mpatches.Patch(color=C["function"],  label="● Function"),

            mpatches.Patch(color=C["class"],     label="● Class"),

            mpatches.Patch(color=C["import"],    label="● Imports"),

            mpatches.Patch(color=C["condition"], label="● Conditions"),

            mpatches.Patch(color=C["loop"],      label="● Loops"),

        ]

        self.ax.legend(handles=legend, loc="lower left",

                       facecolor="#0d0d2a", edgecolor=C["border"],

                       labelcolor=C["text"], fontsize=8, ncol=2,

                       framealpha=0.9)



        self.canvas.draw()



    def _threshold(self):

        xl = self.ax.get_xlim(); yl = self.ax.get_ylim()

        return (0.035 * max(xl[1]-xl[0], yl[1]-yl[0])) ** 2



    def _closest(self, event):

        if not event.inaxes or not self.pos: return None, float("inf")

        best, bd = None, float("inf")

        for nid,(nx_,ny) in self.pos.items():

            d = (event.xdata-nx_)**2 + (event.ydata-ny)**2

            if d < bd: best, bd = nid, d

        return best, bd



    def _click(self, event):

        if event.button != 1: return

        nid, dist = self._closest(event)

        if nid and dist < self._threshold():

            self.selected = nid

            self.draw()

            self.on_select(nid, self.node_meta.get(nid,{}))



    def _hover(self, event):

        if not event.inaxes or not self.pos: return

        nid, dist = self._closest(event)

        if nid and dist < self._threshold() * 1.5:

            meta  = self.node_meta.get(nid,{})

            ntype = meta.get("type","")

            data  = meta.get("data",{})

            color = C.get(ntype, C["file"])



            lines = [f"  {meta.get('label', nid)}  [{ntype.upper()}]  "]

            lines.append("─" * 32)



            if ntype == "file":

                lines += [

                    f"  📄 File: {data.get('path','')}",

                    f"  📌 Lines: {data.get('line_count','?')}",

                    f"  ⚙️   Functions: {len(data.get('functions',[]))}",

                    f"  📦   Classes: {len(data.get('classes',[]))}",

                    f"  📦 Imports: {len(data.get('imports',[]))}",

                    f"  🔀 Conditions: {data.get('conditions',0)}",

                    f"  🔄 Loops: {data.get('loops',0)}",

                ]

            elif ntype == "function":

                args = ", ".join(data.get("args",[]))

                lines += [

                    f"  ⚙️   Function: {data.get('name','')}",

                    f"  📥 Args: ({args or 'none'})",

                    f"  📌 Defined at line {data.get('line','?')}",

                    f"  ⚡ Async: {data.get('is_async',False)}",

                    f"  🔀 Conditions inside: {data.get('conditions',0)}",

                    f"  🔄 Loops inside: {data.get('loops',0)}",

                ]

                if data.get("docstring"):

                    lines.append(f"  📖  {data['docstring'][:55]}…")

            elif ntype == "class":

                methods = [m["name"] for m in data.get("methods",[])]

                lines += [

                    f"  📦   Class: {data.get('name','')}",

                    f"  🔧 Methods: {len(methods)}",

                ]

                if methods:

                    lines.append("     " + ", ".join(methods[:5]))

                if data.get("docstring"):

                    lines.append(f"  📖  {data['docstring'][:55]}…")

            elif ntype == "import":

                imp_list = data if isinstance(data,list) else []

                lines.append(f"  📦 {len(imp_list)} imports:")

                for i in imp_list[:7]:

                    lines.append(f"     • {i}")

                if len(imp_list) > 7:

                    lines.append(f"     … and {len(imp_list)-7} more")

            elif ntype == "condition":

                lines += [

                    f"  🔀 {data.get('conditions',0)} condition blocks",

                    "  (if / else / try / except)",

                ]

            elif ntype == "loop":

                lines += [

                    f"  🔄 {data.get('loops',0)} loop blocks",

                    "  (for / while loops)",

                ]



            lines.append("─" * 32)

            lines.append("  👆 Click to get AI explanation  ")



            x, y = self.pos[nid]

            if self._ann:

                try: self._ann.remove()

                except: pass



            self._ann = self.ax.annotate(

                "\n".join(lines),

                xy=(x, y), xytext=(x+0.1, y+0.1),

                fontsize=7.5, fontfamily="monospace", color=C["text"],

                bbox=dict(boxstyle="round,pad=0.6", fc="#0d0d2a",

                          ec=color, lw=2, alpha=0.97),

                zorder=20,

            )

            self.canvas.draw()

        else:

            if self._ann:

                try: self._ann.remove()

                except: pass

                self._ann = None

                self.canvas.draw()



    def _scroll(self, event):

        if not event.inaxes: return

        f = 0.82 if event.button == "up" else 1.18

        x, y = event.xdata, event.ydata

        xl, xr = self.ax.get_xlim(); yl, yr = self.ax.get_ylim()

        self.ax.set_xlim([x+(xl-x)*f, x+(xr-x)*f])

        self.ax.set_ylim([y+(yl-y)*f, y+(yr-y)*f])

        self.canvas.draw()



    def _pan_press(self, event):

        if event.button == 2 or (event.button == 1 and event.key == "shift"):

            self._pan_start = (event.xdata, event.ydata)

            self._xlim, self._ylim = self.ax.get_xlim(), self.ax.get_ylim()



    def _pan_move(self, event):

        if self._pan_start and event.inaxes and event.xdata:

            dx = self._pan_start[0] - event.xdata

            dy = self._pan_start[1] - event.ydata

            self.ax.set_xlim(self._xlim[0]+dx, self._xlim[1]+dx)

            self.ax.set_ylim(self._ylim[0]+dy, self._ylim[1]+dy)

            self.canvas.draw()



    def _pan_release(self, event): self._pan_start = None



    def highlight(self, nid):

        self.selected = nid

        self.draw()





# ── AI Explainer ──────────────────────────────────────────────────────────────



class Explainer:

    def __init__(self, settings: AISettings):
        self.client = ChatCompletionsClient(settings)

    def stream(self, messages, on_chunk, max_tokens=1000, cancel_event=None):
        return self.client.stream_chat(
            messages,
            on_chunk,
            max_tokens=max_tokens,
            cancel_event=cancel_event,
        )



    def _prompt(self, node_type, data, file_info):

        src = file_info.get("source","")



        if node_type == "file":

            funcs   = [f["name"] for f in data.get("functions",[])]

            classes = [c["name"] for c in data.get("classes",[])]

            return (

                f"Explain this Python file in detail: {data.get('path','')}\n\n"

                f"Lines: {data.get('line_count','?')}\n"

                f"Functions: {', '.join(funcs) or 'none'}\n"

                f"Classes: {', '.join(classes) or 'none'}\n"

                f"Imports: {', '.join(data.get('imports',[])[:15]) or 'none'}\n"

                f"Conditions: {data.get('conditions',0)}, Loops: {data.get('loops',0)}\n\n"

                f"Source:\n```python\n{src}\n```\n\n"

                "Explain:\n1. Purpose of this file\n2. How each function/class works\n"

                "3. Design pattern used\n4. What a beginner should learn from this\n"

                "5. Anything important to notice"

            )

        elif node_type == "function":

            return (

                f"Explain this Python function deeply: `{data.get('name','')}`\n\n"

                f"Args: {data.get('args',[])}\n"

                f"Async: {data.get('is_async',False)}\n"

                f"Conditions inside: {data.get('conditions',0)}\n"

                f"Loops inside: {data.get('loops',0)}\n"

                f"Docstring: {data.get('docstring','none')}\n\n"

                f"Code:\n```python\n{data.get('source','')}\n```\n\n"

                "Explain:\n1. What this function does step by step\n"

                "2. What each argument means\n3. What it returns\n"

                "4. How the logic flows\n5. Any tricky or clever parts"

            )

        elif node_type == "class":

            methods = [m["name"] for m in data.get("methods",[])]

            return (

                f"Explain this Python class deeply: `{data.get('name','')}`\n\n"

                f"Methods: {', '.join(methods)}\n"

                f"Docstring: {data.get('docstring','none')}\n\n"

                f"Code:\n```python\n{data.get('source','')}\n```\n\n"

                "Explain:\n1. What this class represents\n"

                "2. What each method does\n3. How to use it\n"

                "4. The design pattern\n5. What a beginner should understand"

            )

        elif node_type == "import":

            imp_list = data if isinstance(data,list) else []

            return (

                f"Explain these imports from `{file_info.get('path','')}`:\n\n"

                + "\n".join(f"- {i}" for i in imp_list)

                + "\n\nFor each:\n1. What it does\n2. Why it's used here\n"

                  "3. What breaks without it\n4. Standard library or third-party?"

            )

        elif node_type == "condition":

            return (

                f"This file has {data.get('conditions',0)} condition blocks.\n\n"

                f"Source:\n```python\n{src}\n```\n\n"

                "Explain:\n1. What decisions the code is making\n"

                "2. What edge cases it handles\n3. Error handling approach\n"

                "4. Are the conditions well written?"

            )

        elif node_type == "loop":

            return (

                f"This file has {data.get('loops',0)} loops.\n\n"

                f"Source:\n```python\n{src}\n```\n\n"

                "Explain:\n1. What data is being iterated\n"

                "2. What each loop does\n3. Performance concerns?\n"

                "4. Could any be simplified?"

            )

        return f"Explain this Python code element:\n{data}"





# ── Main App ──────────────────────────────────────────────────────────────────



class App(tk.Tk):

    def __init__(self):
        super().__init__()
        self.title("CodeScope 🔍")
        self.configure(bg=C["bg"])
        self.geometry("1440x880")
        self.minsize(1000, 650)

        self.scan_result   = None
        self._explaining   = False
        self._current_nid  = None
        self._current_meta = {}
        self._last_exp_args = None

        self._ui_queue = queue.Queue()
        self._ui_queue_after_id = None
        self._active_request_cancel = None
        self._settings_error = ""
        try:
            self.settings = load_settings()
        except (OSError, ValueError) as error:
            self.settings = AISettings()
            self._settings_error = str(error)
        self.explainer = Explainer(self.settings)

        self._build_ui()
        self._ui_queue_after_id = self.after(50, self._process_ui_queue)

        if self._settings_error:
            self.status.set(
                f"Could not load AI settings: {self._settings_error} "
                "Open AI Settings to configure them."
            )

        if len(sys.argv) > 1:
            self.after(400, lambda: self._load(sys.argv[1]))

    def _build_ui(self):
        # TOOLBAR
        tb = tk.Frame(self, bg=C["bg"], pady=8)
        tb.pack(fill=tk.X)

        tk.Label(
            tb, text="🔭 CodeScope",
            bg=C["bg"], fg=C["text"],
            font=("Helvetica", 14, "bold")
        ).pack(side=tk.LEFT, padx=14)

        self.path_lbl = tk.Label(
            tb, text="No project loaded",
            bg=C["bg"], fg=C["dim"],
            font=("Courier", 9)
        )
        self.path_lbl.pack(side=tk.LEFT, padx=6)

        tk.Button(
            tb, text="📂 Open Project",
            command=self._open,
            bg=C["file"], fg="white",
            relief=tk.FLAT, padx=12, pady=5,
            cursor="hand2"
        ).pack(side=tk.RIGHT, padx=6)

      
        tk.Button(
            tb, text="⚙ AI Settings",
            command=self._settings_dialog,
            bg=C["border"], fg=C["text"],
            relief=tk.FLAT, padx=12, pady=5,
            cursor="hand2"
        ).pack(side=tk.RIGHT, padx=6)

        # MAIN LAYOUT
        pw = tk.PanedWindow(
            self, orient=tk.HORIZONTAL,
            bg=C["bg"], sashwidth=5,
            sashrelief=tk.FLAT
        )
        pw.pack(fill=tk.BOTH, expand=True, padx=8, pady=4)

        # LEFT SIDEBAR
        left = tk.Frame(pw, bg=C["panel"], width=200)
        pw.add(left, minsize=150)

        tk.Label(
            left, text="PROJECT FILES",
            bg=C["panel"], fg=C["dim"],
            font=("Helvetica", 9, "bold")
        ).pack(anchor="w", padx=12, pady=(12, 6))

        self.flist = tk.Listbox(
            left,
            bg=C["panel"], fg=C["text"],
            selectbackground=C["file"],
            selectforeground="white",
            relief=tk.FLAT, borderwidth=0,
            font=("Courier", 9),
            activestyle="none"
        )
        self.flist.pack(fill=tk.BOTH, expand=True, padx=6, pady=6)
        self.flist.bind("<<ListboxSelect>>", self._list_select)

        tk.Label(
            left, text="SYNTAX ERRORS",
            bg=C["panel"], fg=C["dim"],
            font=("Helvetica", 9, "bold")
        ).pack(anchor="w", padx=12, pady=(12, 4))

        self.error_list = tk.Listbox(
            left,
            bg=C["panel"], fg=C["text"],
            selectbackground=C["condition"],
            selectforeground="white",
            relief=tk.FLAT, borderwidth=0,
            font=("Courier", 9),
            height=6,
            activestyle="none"
            
  )
        
        self.error_list.pack(fill=tk.X, expand=False, padx=6, pady=6)
        self.error_list.bind("<<ListboxSelect>>", self._error_selected)

        
        # CENTER GRAPH
        centre = tk.Frame(pw, bg=C["bg"])
        pw.add(centre, minsize=300)

        self.graph = CodeGraph(
            centre,
            on_select_cb=self._node_selected
        )

        # RIGHT DETAIL PANEL
        right = tk.Frame(pw, bg=C["panel"], width=280)
        pw.add(right, minsize=220)

        tk.Label(
            right, text="NODE DETAILS",
            bg=C["panel"], fg=C["dim"],
            font=("Helvetica", 9, "bold")
        ).pack(anchor="w", padx=12, pady=(12, 6))

        self.det_title = tk.Label(
            right, text="Select a node",
            bg=C["panel"], fg=C["text"],
            font=("Helvetica", 12, "bold"),
            wraplength=250
        )
        self.det_title.pack(anchor="w", padx=12, pady=4)

        self.det_type = tk.Label(
            right, text="",
            bg=C["panel"], fg=C["file"],
            font=("Courier", 9)
        )
        self.det_type.pack(anchor="w", padx=12)

        self.det_meta = tk.Label(
            right, text="",
            bg=C["panel"], fg=C["dim"],
            font=("Courier", 9),
            wraplength=250, justify=tk.LEFT
        )
        self.det_meta.pack(anchor="w", padx=12, pady=6)

        # ACTION BUTTONS
        actions = tk.Frame(right, bg=C["panel"])
        actions.pack(fill=tk.X, padx=8, pady=8)

        self.exp_btn = tk.Button(
            actions, text="📖 Deep Explain",
            command=lambda: self._explain_current(simple=False),
            bg="#8056D9", fg="white",
            relief=tk.FLAT, padx=8, pady=6,
            cursor="hand2",
            state=tk.DISABLED
        )
        self.exp_btn.pack(fill=tk.X, pady=3)

        self.simple_btn = tk.Button(
            actions, text="🧠 Simplify",
            command=lambda: self._explain_current(simple=True),
            bg=C["simplify"], fg="white",
            relief=tk.FLAT, padx=8, pady=6,
            cursor="hand2",
            state=tk.DISABLED
        )
        self.simple_btn.pack(fill=tk.X, pady=3)
        # EXPLANATION BOX
        tk.Label(
            right, text="EXPLANATION",
            bg=C["panel"], fg=C["dim"],
            font=("Helvetica", 9, "bold")
        ).pack(anchor="w", padx=12, pady=(12, 4))

        self.exp_box = scrolledtext.ScrolledText(
            right,
            bg=C["bg"], fg=C["text"],
            insertbackground=C["text"],
            relief=tk.FLAT, borderwidth=0,
            font=("Helveticself.cancela", 10),
            wrap=tk.WORD, height=12
        )
        self.exp_box.pack(
            fill=tk.BOTH, expand=True,
            padx=8, pady=(0, 8)
        )
        self.exp_box.insert(
            tk.END,
            "Select a node in the graph to explore it."
        )
        self.exp_box.config(state=tk.DISABLED)

        # STATUS BAR
        self.status = tk.StringVar(value="Ready — open a Python project.")
        status_lbl = tk.Label(
            self, textvariable=self.status,
            bg=C["bg"], fg=C["dim"],
            anchor="w", font=("Courier", 9),
            padx=12, pady=5
        )
        status_lbl.pack(fill=tk.X)

    def _post_ui(self, callback):
        self._ui_queue.put(callback)

    def _process_ui_queue(self):
        self._ui_queue_after_id = None
        while True:
            try:
                callback = self._ui_queue.get_nowait()
            except queue.Empty:
                break
            callback()
        if self.winfo_exists():
            self._ui_queue_after_id = self.after(50, self._process_ui_queue)

    def destroy(self):
        if self._ui_queue_after_id:
            try:
                self.after_cancel(self._ui_queue_after_id)
            except tk.TclError:
                pass
            self._ui_queue_after_id = None
        super().destroy()

    def _settings_dialog(self):
        dialog = tk.Toplevel(self)
        dialog.title("AI Settings")
        dialog.configure(bg=C["panel"])
        dialog.transient(self)
        dialog.grab_set()

        form = tk.Frame(dialog, bg=C["panel"], padx=18, pady=16)
        form.pack(fill=tk.BOTH, expand=True)

        saved_provider = self.settings.provider
        provider_options = list(PROVIDERS)
        if saved_provider == PROVIDER_COMPATIBLE:
            provider_options.append(PROVIDER_COMPATIBLE)
        initial_provider = (
            saved_provider
            if saved_provider in provider_options
            and (self.settings.api_key or saved_provider == PROVIDER_COMPATIBLE)
            else ""
        )
        provider_var = tk.StringVar(value=initial_provider)
        provider_manually_selected = [False]

        tk.Label(
            form, text="API key (leave blank to keep the saved key)",
            bg=C["panel"], fg=C["text"], font=("Helvetica", 9, "bold"),
        ).grid(row=0, column=0, sticky=tk.W, pady=(0, 3))
        api_key_entry = tk.Entry(form, show="*", width=45)
        api_key_entry.grid(row=1, column=0, sticky=tk.EW)
        show_key_var = tk.BooleanVar(value=False)

        def toggle_key_visibility():
            api_key_entry.configure(show="" if show_key_var.get() else "*")

        tk.Checkbutton(
            form, text="Show API key", variable=show_key_var,
            command=toggle_key_visibility, bg=C["panel"], fg=C["text"],
            activebackground=C["panel"], selectcolor=C["bg"],
        ).grid(row=2, column=0, sticky=tk.W)

        tk.Label(
            form, text=credential_storage_description(),
            bg=C["panel"], fg=C["dim"], font=("Helvetica", 8),
        ).grid(row=3, column=0, sticky=tk.W, pady=(2, 0))

        provider_label = tk.Label(
            form, text="Provider (select only if the key format is ambiguous)",
            bg=C["panel"], fg=C["text"], font=("Helvetica", 9, "bold"),
        )
        provider_box = ttk.Combobox(
            form, textvariable=provider_var, values=provider_options,
            state="readonly", width=42,
        )

        def set_provider_picker_visible(visible):
            if visible:
                provider_label.grid(row=4, column=0, sticky=tk.W, pady=(12, 3))
                provider_box.grid(row=5, column=0, sticky=tk.EW)
            else:
                provider_label.grid_remove()
                provider_box.grid_remove()

        set_provider_picker_visible(False)
        clear_key_var = tk.BooleanVar(value=False)
        tk.Checkbutton(
            form, text="Remove saved API key", variable=clear_key_var,
            bg=C["panel"], fg=C["text"], activebackground=C["panel"],
            selectcolor=C["bg"],
        ).grid(row=6, column=0, sticky=tk.W)

        tk.Label(
            form, text="Model", bg=C["panel"], fg=C["text"],
            font=("Helvetica", 9, "bold"),
        ).grid(row=7, column=0, sticky=tk.W, pady=(12, 3))

        selected_model = [self.settings.model]
        model_var = tk.StringVar(value=self.settings.model)
        model_box = ttk.Combobox(
            form, textvariable=model_var, values=([self.settings.model] if self.settings.model else []),
            state="readonly", width=42,
        )
        model_box.grid(row=8, column=0, sticky=tk.EW)

        test_status = tk.StringVar(value="")
        tk.Label(
            form,
            text=(
                "Refresh Models loads the models available to your API key. "
                "Test Connection sends a real request and may use provider quota."
            ),
            bg=C["panel"], fg=C["dim"], wraplength=380, justify=tk.LEFT,
        ).grid(row=9, column=0, sticky=tk.W, pady=(8, 0))
        tk.Label(
            form, textvariable=test_status, bg=C["panel"], fg=C["dim"],
            wraplength=380, justify=tk.LEFT,
        ).grid(row=10, column=0, sticky=tk.W, pady=(10, 0))

        def model_changed(_event=None):
            selected_model[0] = model_var.get().strip()
            test_status.set("")

        model_box.bind("<<ComboboxSelected>>", model_changed)

        def provider_changed(_event=None):
            provider_manually_selected[0] = True
            clear_key_var.set(False)
            selected_model[0] = ""
            model_var.set("")
            model_box.configure(values=())
            test_status.set("")

        def key_changed(_event=None):
            if provider_manually_selected[0]:
                return
            key = api_key_entry.get().strip()
            if not key:
                provider_var.set(initial_provider)
                selected_model[0] = (
                    self.settings.model if initial_provider == saved_provider else ""
                )
                model_var.set(selected_model[0])
                set_provider_picker_visible(False)
                test_status.set("")
                return
            provider = infer_provider_from_api_key(key)
            if provider and provider in provider_options:
                provider_var.set(provider)
                selected_model[0] = ""
                model_var.set("")
                model_box.configure(values=())
                set_provider_picker_visible(False)
                test_status.set(f"Detected {provider} from the API key format.")
            else:
                provider_var.set("")
                selected_model[0] = ""
                model_var.set("")
                model_box.configure(values=())
                set_provider_picker_visible(True)
                test_status.set("This key format is ambiguous; select its provider.")

        provider_box.bind("<<ComboboxSelected>>", provider_changed)
        api_key_entry.bind("<KeyRelease>", key_changed)
        api_key_entry.bind("<<Paste>>", key_changed)
        api_key_entry.bind("<FocusOut>", key_changed)

        def draft_settings():
            provider = provider_var.get()
            if provider not in provider_options:
                raise AIProviderError(
                    "Enter a key with a recognized provider format or select its provider."
                )
            credentials = dict(self.settings.credentials)
            if self.settings.api_key:
                credentials.setdefault(self.settings.provider, self.settings.api_key)
            key = (
                "" if clear_key_var.get()
                else api_key_entry.get().strip() or credentials.get(provider, "")
            )
            if key:
                credentials[provider] = key
            return AISettings(
                provider=provider,
                api_key=key,
                model=model_var.get().strip(),
                base_url=(
                    self.settings.base_url if provider == PROVIDER_COMPATIBLE else ""
                ),
                credentials=credentials,
            )

        def finish_models(models, button, error=None):
            if not dialog.winfo_exists():
                return
            button.config(state=tk.NORMAL)
            if error:
                test_status.set(error)
                return
            if not models:
                test_status.set("No compatible text-generation models were found.")
                return
            model_box.configure(values=models)
            current = selected_model[0]
            if current not in models:
                current = models[0]
            selected_model[0] = current
            model_var.set(current)
            test_status.set(f"Loaded {len(models)} available models.")

        def refresh_models():
            try:
                config = draft_settings()
                if not config.api_key:
                    raise AIProviderError("Add an API key before refreshing models.")
            except AIProviderError as error:
                test_status.set(str(error))
                return
            refresh_button.config(state=tk.DISABLED)
            test_status.set("Loading available models…")

            def work():
                try:
                    client = ChatCompletionsClient(config)
                    models = client.discover_models()
                    error = None
                except AIProviderError as exc:
                    models = []
                    error = str(exc)
                except Exception as exc:
                    models = []
                    error = f"Could not load models: {type(exc).__name__}: {exc}"
                self._post_ui(lambda: finish_models(models, refresh_button, error))

            threading.Thread(target=work, daemon=True).start()

        result_model = [""]

        def finish_test(result, button, suggested_model=None):
            if not dialog.winfo_exists():
                return
            if suggested_model:
                selected_model[0] = suggested_model
                model_var.set(suggested_model)
                values = list(model_box.cget("values"))
                if suggested_model not in values:
                    values.append(suggested_model)
                model_box.configure(values=values)
                result += "\nAnother available model was selected. Test again to verify it."
            elif result.startswith("Connection successful") and result_model[0]:
                selected_model[0] = result_model[0]
                model_var.set(result_model[0])
                values = list(model_box.cget("values"))
                if result_model[0] not in values:
                    values.insert(0, result_model[0])
                model_box.configure(values=values)
            test_status.set(result)
            button.config(state=tk.NORMAL)

        def test_connection():
            try:
                config = draft_settings()
            except AIProviderError as error:
                test_status.set(str(error))
                return
            test_button.config(state=tk.DISABLED)
            test_status.set("Testing the selected model…" if config.model else "Selecting a model and testing the connection…")

            def work():
                client = ChatCompletionsClient(config)
                try:
                    client.stream_chat(
                        [{"role": "user", "content": "Reply with OK."}],
                        lambda _chunk: None,
                        max_tokens=8,
                    )
                    result = "Connection successful. The selected model is ready."
                    suggested = None
                except AIProviderError as error:
                    result = str(error)
                    suggested = error.suggested_model
                except Exception as error:
                    result = f"Connection test failed: {type(error).__name__}: {error}"
                    suggested = None
                result_model[0] = client.selected_model
                self._post_ui(lambda: finish_test(result, test_button, suggested))

            threading.Thread(target=work, daemon=True).start()

        def save():
            try:
                config = draft_settings()
                if not config.model:
                    raise AIProviderError("Choose a model or refresh the model list first.")
                if (
                    not config.api_key
                    and not clear_key_var.get()
                    and config.provider != PROVIDER_COMPATIBLE
                ):
                    raise AIProviderError("Add an API key before saving AI settings.")
                legacy_key_remains = save_settings(
                    config, clear_api_key=clear_key_var.get()
                )
                self.settings = load_settings()
            except (OSError, ValueError, AIProviderError) as error:
                messagebox.showerror(
                    "Could Not Save AI Settings", str(error), parent=dialog
                )
                return
            self.explainer = Explainer(self.settings)
            self.status.set(
                "AI settings saved, but the legacy Groq key file could not be removed."
                if legacy_key_remains else "AI settings saved."
            )
            dialog.destroy()

        buttons = tk.Frame(form, bg=C["panel"])
        buttons.grid(row=11, column=0, sticky=tk.E, pady=(14, 0))
        refresh_button = tk.Button(
            buttons, text="Refresh Models", command=refresh_models,
            bg=C["border"], fg=C["text"], relief=tk.FLAT, padx=10,
        )
        refresh_button.pack(side=tk.LEFT, padx=(0, 8))
        test_button = tk.Button(
            buttons, text="Test Connection", command=test_connection,
            bg=C["border"], fg=C["text"], relief=tk.FLAT, padx=10,
        )
        test_button.pack(side=tk.LEFT, padx=(0, 8))
        tk.Button(
            buttons, text="Save", command=save, bg=C["file"], fg="white",
            relief=tk.FLAT, padx=16,
        ).pack(side=tk.LEFT)

        form.columnconfigure(0, weight=1)
        dialog.resizable(False, False)

    def _open(self):
        p = filedialog.askdirectory(title="Select Python Project")
        if p: self._load(p)

    def _open_project(self):
        self._open()

    
    def _load(self, path):
        if isinstance(path, tk.Event):
            return

        self.status.set(f"Scanning {path} ...")
        self.update()

        def work():
            try:
                r = scan_project(path)
                r["errors"] = ErrorAnalyzer().analyze_project(path)
                self._post_ui(lambda: self._loaded(r))
            except Exception as e:
                self._post_ui(
                    lambda error=str(e): self.status.set(
                        f"Error: {error}"
                    )
                )

        threading.Thread(target=work, daemon=True).start()

    def _loaded(self, result):
        self.scan_result = result
        files = result["files"]
        errors = result.get("errors", [])

        self.errors = errors
        self.path_lbl.config(text=result["root"])

        self.status.set(
            f"Loaded {len(files)} files — "
            f"{len(errors)} syntax errors found."
        )

        self.flist.delete(0, tk.END)

        for rel in sorted(files):
            self.flist.insert(tk.END, rel)

        self.error_list.delete(0, tk.END)

        root = Path(result["root"])

        for error in errors:
            try:
                relative = Path(error.file).relative_to(root)
            except ValueError:
                relative = Path(error.file).name

            self.error_list.insert(
                tk.END,
                f"{relative}:{error.line}"
            )

        self.graph.load(result)

    def _error_selected(self, event=None):
        selection = self.error_list.curselection()

        if not selection:
            return

        error = self.errors[selection[0]]

        self.det_title.config(
            text=f"{Path(error.file).name}:{error.line}"
        )

        self.det_type.config(
            text=error.category,
            fg="#E06C75"
        )

        self.det_meta.config(
            text=f"{error.severity}\n{error.message}"
        )

        self.exp_btn.config(state=tk.DISABLED)
        self.simple_btn.config(state=tk.DISABLED)

        self.exp_box.config(state=tk.NORMAL)
        self.exp_box.delete("1.0", tk.END)
        self.exp_box.insert(
            tk.END,
            f"File: {error.file}\n"
            f"Line: {error.line}\n\n"
            f"Error: {error.message}\n\n"
            f"Source:\n{error.source}"
        )
        self.exp_box.config(state=tk.DISABLED)


    
    def _list_select(self, event):
        sel = self.flist.curselection()
        if not sel: return
        rel  = self.flist.get(sel[0])
        nid  = f"file::{rel}"
        meta = self.graph.node_meta.get(nid, {})
        self.graph.highlight(nid)
        self._node_selected(nid, meta)

    def _node_selected(self, nid, meta):
        self._current_nid  = nid
        self._current_meta = meta
        ntype = meta.get("type","")
        label = meta.get("label", nid)
        data  = meta.get("data",{})
        rel   = meta.get("rel","")

        color = C.get(ntype, C["text"])
        self.det_title.config(text=label, fg=color)
        self.det_type.config(text=f"Type: {ntype.upper()}")

        lines = []
        if ntype == "file":
            lines = [
                f"Path:       {data.get('path','')}",
                f"Lines:      {data.get('line_count','?')}",
                f"Functions:  {len(data.get('functions',[]))}",
                f"Classes:    {len(data.get('classes',[]))}",
                f"Imports:    {len(data.get('imports',[]))}",
                f"Conditions: {data.get('conditions',0)}",
                f"Loops:      {data.get('loops',0)}",
            ]
        elif ntype == "function":
            lines = [
                f"Args:   ({', '.join(data.get('args',[]))})",
                f"Line:   {data.get('line','?')}",
                f"Async:  {data.get('is_async',False)}",
                f"Conds:  {data.get('conditions',0)}",
                f"Loops:  {data.get('loops',0)}",
            ]
        elif ntype == "class":
            methods = [m["name"] for m in data.get("methods",[])]
            lines = [f"Methods: {', '.join(methods) or 'none'}"]
        elif ntype == "import":
            lines = [f"• {i}" for i in (data if isinstance(data,list) else [])[:10]]
        elif ntype in ("condition","loop"):
            k = "conditions" if ntype=="condition" else "loops"
            lines = [f"Count: {data.get(k,0)}"]

        self.det_meta.config(text="\n".join(lines))
        self.exp_btn.config(state=tk.NORMAL)
        self.simple_btn.config(state=tk.NORMAL)
        self._set_exp("")

        for i in range(self.flist.size()):
            if self.flist.get(i) == rel:
                self.flist.selection_clear(0, tk.END)
                self.flist.selection_set(i)
                self.flist.see(i); break
    def _explain_current(self, simple=False):
        if not self._current_nid or self._explaining:
            return

        meta = self._current_meta
        ntype = meta.get("type", "")
        data = meta.get("data", {})
        rel = meta.get("rel", "")

        file_info = {}
        if self.scan_result:
            file_info = self.scan_result["files"].get(rel, {})

        mode = "🧑‍💻 Simplify mode" if simple else "🔍 Deep explanation"

        # SIMPLIFY: use the previous Deep Explain output
        if simple:
            previous_explanation = self.exp_box.get(
                "1.0", tk.END
            ).strip()

            if not previous_explanation:
                self.status.set("Run Deep Explain first!")
                return

            prompt = (
                "Simplify the following programming explanation. "
                "Preserve all important technical concepts and names. "
                "Use clear, beginner-friendly language. "
                "Do not invent information or change the original meaning.\n\n"
                + previous_explanation
            )

            system = (
                "You are a precise and patient programming tutor. "
                "Make technical explanations easier to understand "
                "without removing important programming concepts. "
                "Be accurate, practical, and educational."
            )

        # DEEP EXPLAIN: analyze the selected code
        else:
            prompt = self.explainer._prompt(ntype, data, file_info)

            system = (
                "You are an expert Python code analyst and programming instructor. "
                "Explain only what can be established from the supplied source code. "
                "Walk through the actual implementation step by step. "
                "Explain variables, functions, classes, control flow, and dependencies "
                "when they are relevant. Distinguish confirmed behavior from inference. "
                "Never invent missing code or claim that an imported module is used "
                "without evidence. If the source is incomplete, explicitly identify "
                "what cannot be determined."
            )

        self._run_explanation(
            prompt,
            system,
            mode,
            max_tokens=1000
        )
    
    def _deep_explain(self):
        self._explain_current(simple=False)

    def _explain_project(self):
        if not self.scan_result or self._explaining: return
        files = self.scan_result["files"]
        total_funcs = sum(len(i.get("functions",[])) for i in files.values())
        total_cls   = sum(len(i.get("classes",[])) for i in files.values())
        total_lines = sum(i.get("line_count",0) for i in files.values())

        summary = "\n".join(
            f"• {rel} — {info.get('line_count',0)} lines, "
            f"{len(info.get('functions',[]))} funcs, "
            f"{len(info.get('classes',[]))} classes"
            for rel, info in list(files.items())[:30]
        )
        prompt = (
            f"Give a DEEP explanation of this Python project.\n"
            f"Stats: {len(files)} files, {total_lines} lines, "
            f"{total_funcs} functions, {total_cls} classes.\n\n"
            f"Files:\n{summary}\n\n"
            "Explain deeply:\n"
            "1. What this project does overall\n"
            "2. How it's structured and why\n"
            "3. Main components and how they interact\n"
            "4. Patterns or techniques used\n"
            "5. What someone could learn from studying it"
        )

        self.det_title.config(text="Project Overview", fg=C["text"])
        self.det_type.config(text="")
        self.det_meta.config(text="")
        self._run_explanation(
            prompt,
            "You are an expert Python teacher. Be thorough.",
            "Getting deep project overview…",
            max_tokens=1200,
        )

    def _run_explanation(self, prompt, system, status, max_tokens):
        if self._explaining:
            return
        self._set_exp("")
        self.status.set(status)
        self._explaining = True
        self.exp_btn.config(state=tk.DISABLED)
        self.simple_btn.config(state=tk.DISABLED)
        self._active_request_cancel = threading.Event()

        def run():
            failed = False
            cancelled = False
            try:
                cancelled = not self.explainer.stream(
                    [
                        {"role": "system", "content": system},
                        {"role": "user", "content": prompt},
                    ],
                    lambda text: self._post_ui(
                        lambda chunk=text: self._append_exp(chunk)
                    ),
                    max_tokens=max_tokens,
                    cancel_event=self._active_request_cancel,
                )
            except AIProviderError as error:
                failed = True
                self._post_ui(
                    lambda message=str(error): self._append_exp(
                        f"[Error: {message}]"
                    )
                )
            except Exception as error:
                failed = True

                error_message = (
                    f"[Error: {type(error).__name__}: {error}]"
                )

                print(f"[DEBUG] Unexpected AI request failure: {error}")
                import traceback
                traceback.print_exc()

                self._post_ui(
                    lambda message=error_message: self._append_exp(message)
                )
                  
            
            finally:
                self._post_ui(
                    lambda request_failed=failed, request_cancelled=cancelled:
                    self._exp_done(request_failed, request_cancelled)
                )

        threading.Thread(target=run, daemon=True).start()

    def _cancel_explanation(self):
        if self._active_request_cancel:
            self._active_request_cancel.set()
            self.status.set("Cancelling AI request…")

    def _cancel_request(self):
        self._cancel_explanation()

    def _set_exp(self, text):
        self.exp_box.config(state=tk.NORMAL)
        self.exp_box.delete("1.0", tk.END)
        if text: self.exp_box.insert(tk.END, text)
        self.exp_box.config(state=tk.DISABLED)

    def _append_exp(self, text):
        self.exp_box.config(state=tk.NORMAL)
        self.exp_box.insert(tk.END, text)
        self.exp_box.see(tk.END)
        self.exp_box.config(state=tk.DISABLED)

    def _exp_done(self, failed=False, cancelled=False):
        self._explaining = False
        self._active_request_cancel = None

        self.exp_btn.config(state=tk.NORMAL)
        self.simple_btn.config(state=tk.NORMAL)

        
        if cancelled:
            self.status.set("AI request cancelled.")
        else:
            self.status.set("AI request failed." if failed else "Done.")


if __name__ == "__main__":
    App().mainloop()
