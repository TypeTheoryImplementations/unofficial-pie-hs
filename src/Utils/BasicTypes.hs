-- Copyright (C) 2025 Lincoln Sand
-- SPDX-License-Identifier: AGPL-3.0-only

module Utils.BasicTypes where

type Name = String -- [a-zA-Z] or [0-9] or '-' (first character must be a letter); kebab-case allowed

type Renaming = [(Name, Name)]

data ConvertSuccess = ConvertSuccess
