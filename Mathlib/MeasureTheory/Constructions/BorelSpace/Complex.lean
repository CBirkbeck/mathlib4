/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

#align_import measure_theory.constructions.borel_space.complex from "leanprover-community/mathlib"@"bf6a01357ff5684b1ebcd0f1a13be314fc82c0bf"

/-! # Equip `ℂ` with the Borel sigma-algebra -/


noncomputable section

instance (priority := 900) IsROrC.measurableSpace {𝕜 : Type*} [IsROrC 𝕜] : MeasurableSpace 𝕜 :=
  borel 𝕜

instance (priority := 900) IsROrC.borelSpace {𝕜 : Type*} [IsROrC 𝕜] : BorelSpace 𝕜 :=
  ⟨rfl⟩

instance Complex.measurableSpace : MeasurableSpace ℂ :=
  borel ℂ

instance Complex.borelSpace : BorelSpace ℂ :=
  ⟨rfl⟩
