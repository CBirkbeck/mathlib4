import Mathlib.CategoryTheory.Monoidal.OfChosenFiniteProducts.Basic
import Mathlib.Data.FinEnum
import Mathlib.Tactic

universe u u' v v'

inductive ProdWord (S : Type u) : Type u where
  | of : S → ProdWord S
  | prod : ProdWord S → ProdWord S → ProdWord S
  | nil : ProdWord S

def ProdWord.unpack {S : Type u} : ProdWord S → List S
  | .of X => [X]
  | .prod a b => a.unpack ++ b.unpack
  | .nil => []

def ProdWord.map {S : Type u} {S' : Type u'} (f : S → S') : ProdWord S → ProdWord S'
  | .of t => .of (f t)
  | .prod a b => .prod (map f a) (map f b)
  | .nil => .nil

inductive LawvereWord {S : Type u} (op : ProdWord S → S → Type v) :
    ProdWord S → ProdWord S → Type (max v u) where
  | of {P : ProdWord S} {T : S} (f : op P T) :
      LawvereWord op P (.of T)
  | id (P : ProdWord S) :
      LawvereWord op P P
  | comp {P Q R : ProdWord S} :
      LawvereWord op P Q →
      LawvereWord op Q R →
      LawvereWord op P R
  | fst (P Q : ProdWord S) :
      LawvereWord op (P.prod Q) P
  | snd (P Q : ProdWord S) :
      LawvereWord op (P.prod Q) Q
  | lift {T P Q : ProdWord S} :
      LawvereWord op T P →
      LawvereWord op T Q →
      LawvereWord op T (P.prod Q)
  | toNil (P : ProdWord S) :
      LawvereWord op P .nil

structure FiniteLawverePresentation where
  numSort : ℕ
  sortName (S : Fin numSort) :
    String := s!"X_{S}"
  numOps (P : ProdWord (Fin numSort)) (Q : Fin numSort) :
    ℕ
  opName (P : ProdWord (Fin numSort)) (S : Fin numSort) (op : Fin (numOps P S)) :
    String := s!"op_{op}"
  rels {P Q : ProdWord (Fin numSort)} :
    List (Lean.Name × LawvereWord (fun a b => Fin (numOps a b)) P Q ×
      LawvereWord (fun a b => Fin (numOps a b)) P Q)

structure LawvereTheory where
  S : Type u
  hom : ProdWord S → ProdWord S → Type v
  id (P : ProdWord S) : hom P P
  comp {P Q R : ProdWord S} : hom P Q → hom Q R → hom P R
  id_comp {P Q : ProdWord S} (f : hom P Q) : comp (id _) f = f
  comp_id {P Q : ProdWord S} (f : hom P Q) : comp f (id _) = f
  assoc {P Q R W : ProdWord S} (f : hom P Q) (g : hom Q R) (h : hom R W) :
    comp (comp f g) h = comp f (comp g h)
  fst' (P Q : ProdWord S) : hom (P.prod Q) P
  snd' (P Q : ProdWord S) : hom (P.prod Q) Q
  lift' {T P Q : ProdWord S} (f : hom T P) (g : hom T Q) : hom T (P.prod Q)
  lift'_fst' {T P Q : ProdWord S} (f : hom T P) (g : hom T Q) :
    comp (lift' f g) (fst' _ _) = f
  lift'_snd' {T P Q : ProdWord S} (f : hom T P) (g : hom T Q) :
    comp (lift' f g) (snd' _ _) = g
  lift'_unique {T P Q : ProdWord S} {f g : hom T (P.prod Q)} :
    comp f (fst' _ _) = comp g (fst' _ _) →
    comp f (snd' _ _) = comp g (snd' _ _) →
    f = g
  toNil' (P : ProdWord S) : hom P .nil
  toNil'_unique {P : ProdWord S} (f g : hom P .nil) : f = g

namespace LawvereTheory

variable (L : LawvereTheory.{u,v}) (L' : LawvereTheory.{u',v'})

structure Obj : Type u where as : ProdWord L.S

instance : CoeSort LawvereTheory (Type _) where coe := Obj

open CategoryTheory

instance : Category.{v} L where
  Hom X Y := L.hom X.as Y.as
  id X := L.id X.as
  comp := L.comp
  id_comp := L.id_comp
  comp_id := L.comp_id
  assoc := L.assoc

@[simps]
def nil : L := .mk .nil

def toNil (P : L) : P ⟶ L.nil := L.toNil' _

lemma toNil_unique {P : L} (a b : P ⟶ L.nil) : a = b := L.toNil'_unique _ _

instance {P : L} : Unique (P ⟶ L.nil) where
  default := L.toNil _
  uniq _ := L.toNil_unique _ _

@[simps]
def prod (P Q : L) : L := .mk <| P.as.prod Q.as

def fst (P Q : L) : L.prod P Q ⟶ P := L.fst' _ _
def snd (P Q : L) : L.prod P Q ⟶ Q := L.snd' _ _

@[simps!]
def binaryFan (P Q : L) : Limits.BinaryFan P Q := .mk (L.fst _ _) (L.snd _ _)

def lift {T P Q : L} (a : T ⟶ P) (b : T ⟶ Q) : T ⟶ L.prod P Q := L.lift' a b

@[reassoc (attr := simp)]
lemma lift_fst {T P Q : L} (a : T ⟶ P) (b : T ⟶ Q) :
    L.lift a b ≫ L.fst P Q = a :=
  L.lift'_fst' _ _

@[reassoc (attr := simp)]
lemma lift_snd {T P Q : L} (a : T ⟶ P) (b : T ⟶ Q) :
    L.lift a b ≫ L.snd P Q = b :=
  L.lift'_snd' _ _

@[ext]
lemma lift_unique {T P Q : L} (a b : T ⟶ L.prod P Q)
    (hfst : a ≫ L.fst _ _ = b ≫ L.fst _ _)
    (hsnd : a ≫ L.snd _ _ = b ≫ L.snd _ _) :
    a = b :=
  L.lift'_unique hfst hsnd

@[simps!]
def isLimitBinaryFan (P Q : L) : Limits.IsLimit (L.binaryFan P Q) :=
  Limits.BinaryFan.isLimitMk
    (fun S => L.lift S.fst S.snd)
    (by aesop_cat)
    (by aesop_cat)
    (by aesop_cat)

@[ext]
structure Morphism  (L : LawvereTheory.{u,v}) (L' : LawvereTheory.{u',v'}) where
  obj : L → L'
  map {P Q : L} : (P ⟶ Q) → (obj P ⟶ obj Q)
  map_id (P : L) : map (𝟙 P) = 𝟙 (obj P)
  map_comp {P Q R : L} (a : P ⟶ Q) (b : Q ⟶ R) :
    map (a ≫ b) = map a ≫ map b
  toNil (P : L') : P ⟶ (obj L.nil)
  toNil_unique {P : L'} (f g : P ⟶ obj L.nil) : f = g
  fst (P Q : L) : (obj (L.prod P Q)) ⟶ obj P
  snd (P Q : L) : (obj (L.prod P Q)) ⟶ obj Q
  lift {T : L'} {P Q : L} (a : T ⟶ obj P) (b : T ⟶ obj Q) :
    T ⟶ obj (L.prod P Q)
  lift_fst {T : L'} {P Q : L} (a : T ⟶ obj P) (b : T ⟶ obj Q) :
    lift a b ≫ fst P Q = a
  lift_snd {T : L'} {P Q : L} (a : T ⟶ obj P) (b : T ⟶ obj Q) :
    lift a b ≫ snd P Q = b
  lift_unique {T : L'} {P Q : L} {a b : T ⟶ obj (L.prod P Q)} :
    a ≫ fst _ _ = b ≫ fst _ _ →
    a ≫ snd _ _ = b ≫ snd _ _ →
    a = b

attribute [reassoc (attr := simp)]
  Morphism.lift_fst
  Morphism.lift_snd

attribute [ext]
  Morphism.lift_unique

instance {L L' : LawvereTheory} (F : Morphism L L') (P : L') : Unique (P ⟶ F.obj L.nil) where
  default := F.toNil _
  uniq _ := F.toNil_unique _ _

def Morphism.binaryFan {L L' : LawvereTheory}
    (F : Morphism L L') (P Q : L) : Limits.BinaryFan (F.obj P) (F.obj Q) :=
    Limits.BinaryFan.mk (F.fst P Q) (F.snd P Q)

def Morphism.isLimitBinaryFan {L L' : LawvereTheory}
    (F : Morphism L L') (P Q : L) : Limits.IsLimit (F.binaryFan P Q) :=
  Limits.BinaryFan.isLimitMk
    (fun S => F.lift S.fst S.snd)
    (by aesop_cat)
    (by aesop_cat)
    (by aesop_cat)

@[simps]
def Morphism.functor {L L' : LawvereTheory} (F : Morphism L L') : L ⥤ L' where
  obj := F.obj
  map := F.map
  map_id := F.map_id
  map_comp := F.map_comp

@[simps!]
def Morphism.preservesProd {L L' : LawvereTheory} (F : Morphism L L') (P Q : L) :
    F.obj (L.prod P Q) ≅ L'.prod (F.obj P) (F.obj Q) :=
  (F.isLimitBinaryFan P Q).conePointUniqueUpToIso (L'.isLimitBinaryFan _ _)

end LawvereTheory
