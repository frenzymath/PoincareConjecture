import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.FundamentalGroup.PathMaps
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Commensurable



set_option autoImplicit false

namespace FundamentalGroup

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem fundamentalGroupMulEquivOfPath_trans
    {Z : Type*} [TopologicalSpace Z] {x y z : Z}
    (p : Path x y) (q : Path y z) :
    fundamentalGroupMulEquivOfPath (p.trans q) =
      (fundamentalGroupMulEquivOfPath p).trans
        (fundamentalGroupMulEquivOfPath q) := by
  let a := (CategoryTheory.Groupoid.isoEquivHom (FundamentalGroupoid.mk x)
    (FundamentalGroupoid.mk z)).symm
      (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (p.trans q)))
  let ap := (CategoryTheory.Groupoid.isoEquivHom (FundamentalGroupoid.mk x)
    (FundamentalGroupoid.mk y)).symm
      (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk p))
  let aq := (CategoryTheory.Groupoid.isoEquivHom (FundamentalGroupoid.mk y)
    (FundamentalGroupoid.mk z)).symm
      (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk q))
  have ha : a = ap.trans aq := by
    apply CategoryTheory.Iso.ext
    change Path.Homotopic.Quotient.mk (p.trans q) =
      (Path.Homotopic.Quotient.mk p).trans (Path.Homotopic.Quotient.mk q)
    exact (Path.Homotopic.Quotient.mk_trans p q).symm
  change a.conj = ap.conj.trans aq.conj
  rw [ha]
  ext gamma
  exact CategoryTheory.Iso.trans_conj ap aq gamma

theorem fundamentalGroupMulEquivOfPath_symm
    {Z : Type*} [TopologicalSpace Z] {x y : Z} (p : Path x y) :
    fundamentalGroupMulEquivOfPath p.symm =
      (fundamentalGroupMulEquivOfPath p).symm := by
  let a := (CategoryTheory.Groupoid.isoEquivHom (FundamentalGroupoid.mk x)
    (FundamentalGroupoid.mk y)).symm
      (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk p))
  let as := (CategoryTheory.Groupoid.isoEquivHom (FundamentalGroupoid.mk y)
    (FundamentalGroupoid.mk x)).symm
      (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk p.symm))
  have ha : as = a.symm := by
    apply CategoryTheory.Iso.ext
    rfl
  change as.conj = a.symm.conj
  rw [ha]


theorem map_path_change_naturality (f : C(X, Y)) {x₀ x₁ : X} (p : Path x₀ x₁) :
    (map f x₁).comp (fundamentalGroupMulEquivOfPath p).toMonoidHom =
      (fundamentalGroupMulEquivOfPath (p.map f.continuous)).toMonoidHom.comp (map f x₀) := by
  ext gamma
  change Path.Homotopic.Quotient.map
    ((Path.Homotopic.Quotient.mk p).symm.trans
      (gamma.trans (Path.Homotopic.Quotient.mk p))) f =
    (Path.Homotopic.Quotient.mk (p.map f.continuous)).symm.trans
      ((Path.Homotopic.Quotient.map gamma f).trans
        (Path.Homotopic.Quotient.mk (p.map f.continuous)))
  rw [Path.Homotopic.Quotient.map_trans, Path.Homotopic.Quotient.map_trans,
    Path.Homotopic.Quotient.map_symm, Path.Homotopic.Quotient.mk_map]


theorem range_map_path_change (f : C(X, Y)) {x₀ x₁ : X} (p : Path x₀ x₁) :
    (map f x₁).range = (map f x₀).range.map
      (fundamentalGroupMulEquivOfPath (p.map f.continuous)).toMonoidHom := by
  have hr : (fundamentalGroupMulEquivOfPath p).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (fundamentalGroupMulEquivOfPath p).surjective
  rw [MonoidHom.map_range, ← map_path_change_naturality, MonoidHom.range_comp,
    hr, ← MonoidHom.range_eq_map]

theorem range_map_commensurable_of_source_path
    {E₀ E₁ X : Type*} [TopologicalSpace E₀] [TopologicalSpace E₁]
    [TopologicalSpace X]
    (i₀ : C(E₀, X)) (i₁ : C(E₁, X)) (x₀ : E₀) (x₁ : E₁)
    (k₀ : Path (i₀ x₀) (i₁ x₁))
    (hc : (map i₀ x₀).range.Commensurable
      (((fundamentalGroupMulEquivOfPath k₀.symm).toMonoidHom.comp
        (map i₁ x₁)).range))
    {x : E₀} (l : Path x₀ x) :
    (map i₀ x).range.Commensurable
      (((fundamentalGroupMulEquivOfPath
        ((l.map i₀.continuous).symm.trans k₀).symm).toMonoidHom.comp
        (map i₁ x₁)).range) := by
  let q := l.map i₀.continuous
  let Q := (fundamentalGroupMulEquivOfPath q).toMonoidHom
  let H₀ := (map i₀ x₀).range
  let K₀ := ((fundamentalGroupMulEquivOfPath k₀.symm).toMonoidHom.comp
    (map i₁ x₁)).range
  let Hx := (map i₀ x).range
  let Kx := ((fundamentalGroupMulEquivOfPath (q.symm.trans k₀).symm).toMonoidHom.comp
    (map i₁ x₁)).range
  have hH : Hx = H₀.map Q := by
    exact range_map_path_change i₀ l
  have hQ :
      (fundamentalGroupMulEquivOfPath (q.symm.trans k₀).symm).toMonoidHom.comp
          (map i₁ x₁) =
        Q.comp ((fundamentalGroupMulEquivOfPath k₀.symm).toMonoidHom.comp
          (map i₁ x₁)) := by
    ext gamma
    rw [fundamentalGroupMulEquivOfPath_symm,
      fundamentalGroupMulEquivOfPath_trans,
      fundamentalGroupMulEquivOfPath_symm]
    have hs :
        ((fundamentalGroupMulEquivOfPath q).symm.trans
          (fundamentalGroupMulEquivOfPath k₀)).symm =
        (fundamentalGroupMulEquivOfPath k₀).symm.trans
          (fundamentalGroupMulEquivOfPath q) := by
      ext gamma
      rfl
    rw [hs, fundamentalGroupMulEquivOfPath_symm]
    rfl
  have hK : Kx = K₀.map Q := by
    change ((fundamentalGroupMulEquivOfPath (q.symm.trans k₀).symm).toMonoidHom.comp
      (map i₁ x₁)).range = _
    rw [hQ, MonoidHom.range_comp]
  change Hx.Commensurable Kx
  rw [hH, hK]
  constructor
  · rw [Subgroup.relIndex_map_map_of_injective H₀ K₀
      (fundamentalGroupMulEquivOfPath q).injective]
    exact hc.1
  · rw [Subgroup.relIndex_map_map_of_injective K₀ H₀
      (fundamentalGroupMulEquivOfPath q).injective]
    exact hc.2

theorem index_range_map_eq_of_path (f : C(X, Y)) {x₀ x₁ : X} (p : Path x₀ x₁) :
    (map f x₁).range.index = (map f x₀).range.index := by
  rw [range_map_path_change f p]
  exact Subgroup.index_map_of_bijective
    (f := (fundamentalGroupMulEquivOfPath (p.map f.continuous)).toMonoidHom)
    (fundamentalGroupMulEquivOfPath (p.map f.continuous)).bijective _

theorem finiteIndex_range_map_of_path (f : C(X, Y)) {x₀ x₁ : X} (p : Path x₀ x₁)
    (h : (map f x₀).range.FiniteIndex) : (map f x₁).range.FiniteIndex := by
  rw [Subgroup.finiteIndex_iff, index_range_map_eq_of_path f p]
  exact h.index_ne_zero

theorem finiteIndex_range_map_iff_of_path (f : C(X, Y)) {x₀ x₁ : X} (p : Path x₀ x₁) :
    (map f x₁).range.FiniteIndex ↔ (map f x₀).range.FiniteIndex :=
  ⟨finiteIndex_range_map_of_path f p.symm, finiteIndex_range_map_of_path f p⟩


theorem finiteIndex_range_map_all_basepoints [PathConnectedSpace X]
    (f : C(X, Y)) (x₀ : X) (h : (map f x₀).range.FiniteIndex) :
    ∀ x : X, (map f x).range.FiniteIndex := fun x =>
  finiteIndex_range_map_of_path f (PathConnectedSpace.somePath x₀ x) h

end FundamentalGroup
