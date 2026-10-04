import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! Adapted from Mapher `PoincareMT/Proofs/M54/Mathlib/PathMaps.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`; see `references/ricci-flow/mapher/group-effects.md`. -/

/-!
# Functorial path-class identities

The path-class functoriality and cancellation used in the van Kampen
argument of Hatcher Theorem 1.20 (pp. 43-46) and Morgan--Tian
Proposition 15.3 (pp. 357-358).
-/

set_option autoImplicit false

namespace Path.Homotopic

variable {X : Type*} [TopologicalSpace X]

/-- Constant connectors do not change a path class, even when their
endpoint equalities are not definitional (Hatcher Theorem 1.20, pp. 43-46). -/
theorem of_constant_connectors {a b x y : X}
    (c : Path a x) (d : Path b y) (q : Path a b) (p : Path x y)
    (hc : ∀ t, c t = x) (hd : ∀ t, d t = y) (hqp : ∀ t, q t = p t) :
    (c.symm.trans (q.trans d)).Homotopic p := by
  have ha : a = x := c.source.symm.trans (hc 0)
  have hb : b = y := d.source.symm.trans (hd 0)
  subst a
  subst b
  have hc' : c = Path.refl x := Path.ext (funext hc)
  have hd' : d = Path.refl y := Path.ext (funext hd)
  have hq' : q = p := Path.ext (funext hqp)
  rw [hc', hd', hq', Path.refl_symm]
  exact (refl_trans _).trans (trans_refl p)

end Path.Homotopic

/-- Paths in a simply connected subset are homotopic in the ambient
space, with endpoints fixed (Hatcher Theorem 1.20, pp. 43-46). -/
theorem IsSimplyConnected.paths_homotopic_of_mem
    {X : Type*} [TopologicalSpace X] {s : Set X} (hs : IsSimplyConnected s)
    {x y : X} (p q : Path x y) (hp : ∀ t, p t ∈ s) (hq : ∀ t, q t ∈ s) :
    p.Homotopic q := by
  let : SimplyConnectedSpace s := hs
  let xS : s := ⟨x, by simpa using hp 0⟩
  let yS : s := ⟨y, by simpa using hp 1⟩
  let pS : Path xS yS :=
    ⟨⟨fun t => ⟨p t, hp t⟩, p.continuous.subtype_mk hp⟩,
      Subtype.ext p.source, Subtype.ext p.target⟩
  let qS : Path xS yS :=
    ⟨⟨fun t => ⟨q t, hq t⟩, q.continuous.subtype_mk hq⟩,
      Subtype.ext q.source, Subtype.ext q.target⟩
  obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic pS qS
  exact ⟨(H.map ⟨Subtype.val, continuous_subtype_val⟩).cast (by ext t; rfl) (by ext t; rfl)⟩

namespace Path.Homotopic.Quotient

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Mapping path classes preserves composition, as used in the proof of
Hatcher Theorem 1.20, pp. 43-46. -/
@[simp] theorem map_trans {x y z : X} (p : Path.Homotopic.Quotient x y)
    (q : Path.Homotopic.Quotient y z) (f : C(X, Y)) :
    (p.trans q).map f = (p.map f).trans (q.map f) := by
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
    induction q using Path.Homotopic.Quotient.ind with
    | mk q => exact congrArg Path.Homotopic.Quotient.mk (Path.map_trans p q f.continuous)

/-- Mapping path classes preserves reversal, as used in the proof of
Hatcher Theorem 1.20, pp. 43-46. -/
@[simp] theorem map_symm {x y : X} (p : Path.Homotopic.Quotient x y) (f : C(X, Y)) :
    p.symm.map f = (p.map f).symm := by
  induction p using Path.Homotopic.Quotient.ind with
  | mk p => rfl

/-- Mapping a constant path gives a constant path, as used in
Hatcher Theorem 1.20, pp. 43-46. -/
@[simp] theorem map_refl (x : X) (f : C(X, Y)) : (refl x).map f = refl (f x) := rfl

/-- The identity continuous map acts trivially on path classes, as used in
Hatcher Theorem 1.20, pp. 43-46. -/
@[simp] theorem map_id {x y : X} (p : Path.Homotopic.Quotient x y) :
    p.map (.id X) = p := by
  induction p using Path.Homotopic.Quotient.ind with
  | mk p => rfl

/-- Cancel a path followed by its inverse, without changing the trailing
path (Hatcher Theorem 1.20 construction, pp. 43-46). -/
@[simp] theorem trans_symm_assoc {x y z : X} (p : Path.Homotopic.Quotient x y)
    (q : Path.Homotopic.Quotient x z) : p.trans (p.symm.trans q) = q := by
  rw [← trans_assoc, trans_symm, refl_trans]

/-- Cancel an inverse followed by its path, without changing the trailing
path (Hatcher Theorem 1.20 construction, pp. 43-46). -/
@[simp] theorem symm_trans_assoc {x y z : X} (p : Path.Homotopic.Quotient x y)
    (q : Path.Homotopic.Quotient y z) : p.symm.trans (p.trans q) = q := by
  rw [← trans_assoc, symm_trans, refl_trans]

end Path.Homotopic.Quotient

namespace FundamentalGroup

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Fundamental-group maps compose in the same order as continuous maps,
as used in Hatcher Theorem 1.20, pp. 43-46. -/
theorem map_comp (f : C(X, Y)) (g : C(Y, Z)) (x : X) :
    map (g.comp f) x = (map g (f x)).comp (map f x) := by
  ext p
  exact Path.Homotopic.Quotient.map_comp

/-- The identity continuous map induces the identity group homomorphism,
as used in Hatcher Theorem 1.20, pp. 43-46. -/
@[simp] theorem map_id (x : X) : map (.id X) x = MonoidHom.id (FundamentalGroup X x) := by
  ext p
  exact Path.Homotopic.Quotient.map_id p

end FundamentalGroup
