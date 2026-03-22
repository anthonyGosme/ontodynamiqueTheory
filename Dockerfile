# =============================================================================
# Ontodynamique — Reproducible Validation Environment
# =============================================================================
# Pre-built image with ALL dependencies: Python 3.10, Lean 4, MDSINE2.
# No restart, no version conflicts, no 55-minute downloads.
#
# Pull from Docker Hub (recommended):
#   docker pull anthonygosme/ontodynamique:latest
#   docker run --rm -v $(pwd)/output:/app/output anthonygosme/ontodynamique
#
# Or build locally:
#   docker build -t anthonygosme/ontodynamique .
#
# Push to Docker Hub (maintainer only):
#   docker login
#   docker build -t anthonygosme/ontodynamique:latest -t anthonygosme/ontodynamique:v1.0 .
#   docker push anthonygosme/ontodynamique --all-tags
# =============================================================================

FROM python:3.10-bookworm

LABEL maintainer="Anthony Gosme <anthonygosme@gmail.com>"
LABEL description="Ontodynamique — Lean 4 + Cross-Domain Empirical Validation"
LABEL org.opencontainers.image.source="https://github.com/anthonyGosme/ontodynamiqueTheory"
LABEL org.opencontainers.image.documentation="https://www.ontodynamique.com"

# ── System dependencies ──────────────────────────────────────────────────────
RUN apt-get update && apt-get install -y --no-install-recommends \
    libgmp-dev \
    libmpfr-dev \
    && rm -rf /var/lib/apt/lists/*

# ── Lean 4 (via elan) ───────────────────────────────────────────────────────
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf \
    | sh -s -- -y --default-toolchain stable
ENV PATH="/root/.elan/bin:${PATH}"
# Force download of the Lean toolchain now (not at first run)
RUN lean --version

# ── Working directory ────────────────────────────────────────────────────────
WORKDIR /app

# ── Clone project from GitHub ─────────────────────────────────────────────────
RUN git clone --depth 1 https://github.com/anthonyGosme/ontodynamiqueTheory.git .

# ── Python dependencies ──────────────────────────────────────────────────────
RUN pip install --no-cache-dir -r requirements.txt

# ── MDSINE2 (from GitHub) ───────────────────────────────────────────────────
RUN git clone --depth 1 https://github.com/gerberlab/MDSINE2.git /tmp/MDSINE2 \
    && pip install --no-cache-dir /tmp/MDSINE2/ \
    && rm -rf /tmp/MDSINE2

# ── Output directory ─────────────────────────────────────────────────────────
RUN mkdir -p /app/output

# ── Default: run all tests ───────────────────────────────────────────────────
ENTRYPOINT ["python", "run_all_tests.py"]
