import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusFreeBoundaryMotion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem m64C2ShrinkingCurve_free_label_contDiff_two
    (F : RicciFlow n M (Icc a b)) {c : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c (Icc a b)) {t : ℝ} (ht : t ∈ Icc a b)
    {sigma : ℝ → ℝ} (hsigma : Continuous sigma)
    (hanchor : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun x => c (sigma x) t)) :
    ContDiff ℝ 2 sigma := by
  let : Nonempty M := ⟨c 0 t⟩
  obtain ⟨N, e, he, hemb, hinj⟩ := exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
  obtain ⟨U, rho, hU, heU, hrho, hrhoe, _hmin, _huniq⟩ :=
    M63.exists_smooth_compact_embedded_retraction e hemb he hinj
  let f : ℝ → EuclideanSpace ℝ (Fin N) := fun y => e (c y t)
  have he2 : ContMDiff (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) 2 e :=
    he.of_le (by norm_cast)
  have hf : ContDiff ℝ 2 f := (he2.comp (hc.spatial_regular t ht)).contDiff
  have hdata := (M63.c2ShrinkingCurve_embedded_closed_data hc he).2.1
  have hleft := (M63.smooth_retraction_differentials he hU heU hrho hrhoe).2.2
  have hne (y : ℝ) : deriv f y ≠ 0 := by
    have hder : HasDerivAt f
        (mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) e (c y t)
          (curveVelocity (n := n) (fun z => c z t) y)) y := hdata t ht y
    rw [hder.deriv]
    intro hz
    have h := hleft (c y t) (curveVelocity (n := n) (fun z => c z t) y)
    erw [hz, map_zero] at h
    exact hc.immersed t ht y h.symm
  have hfc : ContDiff ℝ 2 (f ∘ sigma) :=
    (he.comp hanchor).contDiff.of_le (by norm_cast)
  exact contDiff_iff_contDiffAt.mpr fun x =>
    M63.contDiffAt_of_comp_immersed_curve (by norm_num) hsigma.continuousAt
      hf.contDiffAt (hne (sigma x)) hfc.contDiffAt

end PoincareConjecture
