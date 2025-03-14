import Lake
open Lake DSL

package moremath where
  -- add package configuration options here

@[default_target]
lean_lib MoreMath where
  srcDir := "src"

-- @[default_target]
lean_exe Main where
  srcDir := "tests"

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.15.0"
