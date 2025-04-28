import Mathlib.CategoryTheory.Sites.Descent.HasEffectiveDescent
import Mathlib.Algebra.Category.ModuleCat.Pseudofunctor
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

universe u

open CategoryTheory

namespace CommRingCat.moduleCatExtendScalarsPseudofunctor

-- this is the key statement in faithfully flat descent

lemma hasEffectiveDescentRelativeTo_of_faithfullyFlat
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]:
    ((mapLocallyDiscrete (opOpEquivalence CommRingCat.{u}).functor).comp
  moduleCatExtendScalarsPseudofunctor).HasEffectiveDescentRelativeTo
    (fun (_ : Unit) ↦ (CommRingCat.ofHom (algebraMap A B)).op) :=
  sorry

end CommRingCat.moduleCatExtendScalarsPseudofunctor
