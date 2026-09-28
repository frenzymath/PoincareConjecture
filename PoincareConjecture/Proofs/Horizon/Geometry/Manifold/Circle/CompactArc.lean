import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.Order.Compact










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric IsManifold
open scoped Manifold ContDiff

namespace Poincare.Geometry.Manifold.Circle

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev S1 := sphere (0 : EuclideanSpace Real (Fin 2)) 1
private instance : Fact (Module.finrank Real (EuclideanSpace Real (Fin 2)) = 1 + 1) :=
  ⟨by simp⟩


theorem exists_real_stereographic_chart (p : S1) :
    ∃ e : OpenPartialHomeomorph Real S1,
      e.source = univ ∧ e.target = {p}ᶜ ∧
      ContMDiff 𝓘(Real, Real) (𝓡 1) ∞ e ∧
      ContMDiffOn (𝓡 1) 𝓘(Real, Real) ∞ e.symm e.target ∧
      Function.Injective e := by
  let A : Real ≃L[Real] E1 :=
    ((EuclideanSpace.equiv (Fin 1) Real).trans
      (LinearEquiv.funUnique (Fin 1) Real Real).toContinuousLinearEquiv).symm
  let c := stereographic' 1 p
  have hc : c ∈ maximalAtlas (𝓡 1) ∞ S1 :=
    IsManifold.subset_maximalAtlas ⟨p, rfl⟩
  have hcs : ContMDiff (𝓡 1) (𝓡 1) ∞ c.symm := by
    rw [← contMDiffOn_univ]
    simpa only [c, stereographic'_target] using contMDiffOn_symm_of_mem_maximalAtlas hc
  let e := A.toHomeomorph.toOpenPartialHomeomorph.trans c.symm
  have hes : e.source = univ := by simp [e, c]
  have het : e.target = {p}ᶜ := by simp [e, c]
  refine ⟨e, hes, het, hcs.comp A.contDiff.contMDiff, ?_, ?_⟩
  · simpa [e, c] using
      A.symm.contDiff.contMDiff.comp_contMDiffOn (contMDiffOn_of_mem_maximalAtlas hc)
  · intro x y hxy
    exact e.injOn (hes ▸ mem_univ x) (hes ▸ mem_univ y) hxy



theorem exists_interval_parametrization_of_compact_connected
    {K : Set S1} (hK : IsCompact K) (hconn : IsConnected K)
    (p : S1) (hp : p ∉ K) :
    ∃ (e : OpenPartialHomeomorph Real S1) (a b : Real),
      e.source = univ ∧ e.target = {p}ᶜ ∧
      ContMDiff 𝓘(Real, Real) (𝓡 1) ∞ e ∧
      ContMDiffOn (𝓡 1) 𝓘(Real, Real) ∞ e.symm e.target ∧
      Function.Injective e ∧ a ≤ b ∧ e '' Icc a b = K ∧
      (K.Nontrivial → a < b) := by
  obtain ⟨e, hes, het, he, hei, heinj⟩ := exists_real_stereographic_chart p
  have hKt : K ⊆ e.target := by
    intro x hx
    rw [het]
    simpa only [mem_compl_iff, mem_singleton_iff] using ne_of_mem_of_not_mem hx hp
  have hcont : ContinuousOn e.symm K := e.continuousOn_symm.mono hKt
  have hcompact : IsCompact (e.symm '' K) := hK.image_of_continuousOn hcont
  have hconnected : IsConnected (e.symm '' K) := hconn.image _ hcont
  have hinterval := eq_Icc_of_connected_compact hconnected hcompact
  have hle : sInf (e.symm '' K) ≤ sSup (e.symm '' K) :=
    csInf_le_csSup hconnected.nonempty hcompact.bddBelow hcompact.bddAbove
  have himage : e '' Icc (sInf (e.symm '' K)) (sSup (e.symm '' K)) = K := by
    rw [← hinterval]
    ext x
    constructor
    · rintro ⟨t, ⟨y, hy, rfl⟩, rfl⟩
      simpa only [e.right_inv (hKt hy)] using hy
    · intro hx
      exact ⟨e.symm x, ⟨x, hx, rfl⟩, e.right_inv (hKt hx)⟩
  refine ⟨e, _, _, hes, het, he, hei, heinj, hle, himage, ?_⟩
  intro hn
  refine lt_of_le_of_ne hle ?_
  intro hab
  rw [hab, Icc_self, image_singleton] at himage
  exact hn.not_subsingleton (himage ▸ subsingleton_singleton)

end Poincare.Geometry.Manifold.Circle
