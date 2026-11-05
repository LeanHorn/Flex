#!/usr/bin/env python3
"""RQ3b: CHC-COMP, using the same measurement harness as RQ3a."""
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'RQ3a'))
from benchmark import main

if __name__ == '__main__':
    main(study='b')
