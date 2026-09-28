import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsTubeLabels

set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

local notation "P" => (ℝ × E2)

theorem exists_stackTubeEndFamily
    (T : OpenPartialHomeomorph P P)
    (hT : ContDiffOn ℝ ∞ T T.source)
    (hTi : ContDiffOn ℝ ∞ T.symm T.target)
    (hTh : ∀ p ∈ T.source, (T p).1 = p.1)
    (c : ℝ → UnitCircle → E2) (c0 c1 jL jR : ℝ)
    (hP : PlanarSchoenfliesService) (hc01 : c0 < c1)
    (hc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
      (fun p : ℝ × UnitCircle => c p.1 p.2))
    (hce : ∀ z ∈ Icc c0 c1, IsPlanarEmbedding (c z))
    (hJband : Ioo jL jR ⊆ Icc c0 c1)
    (hsource : Ioo jL jR ×ˢ closedBall (0 : E2) 1 ⊆ T.source)
    (hcircle : ∀ z ∈ Ioo jL jR, ∀ q : UnitCircle,
      (T (z, (q : E2))).2 ∈ range (c z))
    (A B : ℝ) (hLA : jL < A) (hAB : A ≤ B) (hBR : B < jR) :
    ∃ R : E2 ≃ₗᵢ[ℝ] E2,
      (R = LinearIsometryEquiv.refl ℝ E2 ∨
        R = Complex.orthonormalBasisOneI.repr.symm.trans
          (Complex.conjLIE.trans Complex.orthonormalBasisOneI.repr)) ∧
      ∃ cbar : ℝ → UnitCircle → E2,
        ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
          (fun p : ℝ × UnitCircle => cbar p.1 p.2) ∧
        (∀ z ∈ Icc c0 c1, IsPlanarEmbedding (cbar z)) ∧
        (∀ z : ℝ, range (cbar z) = range (c z)) ∧
        (∀ z ∉ Ioo jL jR, ∀ q : UnitCircle, cbar z q = c z q) ∧
        ∃ D : PlanarSchoenfliesFamilyData cbar c0 c1,
          ∃ G : PlanarFamilyGraphChart D,
            ∃ Trot : OpenPartialHomeomorph P P,
              Trot.source = {p : P | (p.1, R p.2) ∈ T.source} ∧
              Trot.target = T.target ∧
              (∀ p : P, Trot p = T (p.1, R p.2)) ∧
              (∀ p : P, Trot.symm p = ((T.symm p).1, R.symm (T.symm p).2)) ∧
              ContDiffOn ℝ ∞ Trot Trot.source ∧
              ContDiffOn ℝ ∞ Trot.symm Trot.target ∧
              (∀ p ∈ Trot.source, (Trot p).1 = p.1) ∧
              (∀ p ∈ Trot.target, (Trot.symm p).1 = p.1) ∧
              Ioo jL jR ×ˢ closedBall (0 : E2) 1 ⊆ Trot.source ∧
              ∀ z ∈ Icc A B, ∀ q ∈ sphere (0 : E2) 1,
                Trot (z, q) = G.chart (z, q) := by
  classical
  let : Fact (Module.finrank ℝ E2 = 1 + 1) := ⟨by simp [E2]⟩
  obtain ⟨D0⟩ := hP.2 c0 c1 c hc01 hc hce
  obtain ⟨G0⟩ := D0.nonempty_graphChart hc01
  have hJ : jL < jR := (hLA.trans_le hAB).trans hBR
  obtain ⟨phi, hphi, _hphii, hlabels, _hphiout⟩ :=
    exists_stackTubeEndLabels T hT hTi hTh c c0 c1 jL jR D0 G0
      hJ hJband hsource hcircle
  obtain ⟨R, hR, L, hL, _hLi, hLagree, hLout⟩ :=
    exists_stackClippedCircleLabels phi jL A B jR hLA hAB hBR hphi
  let cbar : ℝ → UnitCircle → E2 := fun z q => c z (L z q)
  have hcb : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
      (fun p : ℝ × UnitCircle => cbar p.1 p.2) :=
    hc.comp (contMDiff_fst.prodMk hL)
  have hcbe (z : ℝ) (hz : z ∈ Icc c0 c1) : IsPlanarEmbedding (cbar z) := by
    have hcz := hce z hz
    refine ⟨hcz.1.comp (L z).contMDiff_toFun,
      hcz.2.1.comp (L z).injective, ?_⟩
    intro q
    change Injective (mfderiv (𝓡 1) 𝓘(ℝ, E2) (c z ∘ L z) q)
    rw [mfderiv_comp q (hcz.1.mdifferentiable (by simp) _)
      ((L z).mdifferentiable (by simp) q)]
    exact (hcz.2.2 _).comp
      (((L z).toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective (mem_univ q))
  have hrange (z : ℝ) : range (cbar z) = range (c z) :=
    (L z).surjective.range_comp (c z)
  have hout (z : ℝ) (hz : z ∉ Ioo jL jR) (q : UnitCircle) : cbar z q = c z q := by
    change c z (L z q) = c z q
    rw [hLout z hz q]
  obtain ⟨D⟩ := hP.2 c0 c1 cbar hc01 hcb hcbe
  obtain ⟨G⟩ := D.nonempty_graphChart hc01
  let V := (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr R.toContinuousLinearEquiv
  let Trot := V.toHomeomorph.transOpenPartialHomeomorph T
  have hTr : ContDiffOn ℝ ∞ Trot Trot.source :=
    hT.comp V.contDiff.contDiffOn (fun _ hp => hp)
  have hTri : ContDiffOn ℝ ∞ Trot.symm Trot.target :=
    V.symm.contDiff.comp_contDiffOn hTi
  have hTrh (p : P) (hp : p ∈ Trot.source) : (Trot p).1 = p.1 :=
    hTh (p.1, R p.2) hp
  have hTrih (p : P) (hp : p ∈ Trot.target) : (Trot.symm p).1 = p.1 := by
    have hh := hTrh (Trot.symm p) (Trot.map_target hp)
    rw [Trot.right_inv hp] at hh
    exact hh.symm
  have hTrsource : Ioo jL jR ×ˢ closedBall (0 : E2) 1 ⊆ Trot.source := by
    intro p hp
    change (p.1, R p.2) ∈ T.source
    exact hsource ⟨hp.1, mem_closedBall_zero_iff.mpr (by
      rw [R.norm_map]
      exact mem_closedBall_zero_iff.mp hp.2)⟩
  refine ⟨R, hR, cbar, hcb, hcbe, hrange, hout, D, G, Trot,
    rfl, rfl, fun _ => rfl, fun _ => rfl, hTr, hTri, hTrh, hTrih, hTrsource, ?_⟩
  intro z hz q hq
  have hband : z ∈ Ioo jL jR :=
    (Icc_subset_Ioo_iff hAB).mpr ⟨hLA, hBR⟩ hz
  let q' : UnitCircle := ⟨R q, by simpa only [mem_sphere_zero_iff_norm, R.norm_map] using hq⟩
  have he : cbar z ⟨q, hq⟩ = (Trot (z, q)).2 := by
    change c z (L z ⟨q, hq⟩) = _
    rw [hLagree z hz]
    exact (hlabels z hband q').2.2
  apply Prod.ext
  · rw [G.chart_apply]
    exact hTrh _ (hTrsource ⟨hband, sphere_subset_closedBall hq⟩)
  · rw [G.chart_apply, D.chart_boundary z (hJband hband) ⟨q, hq⟩]
    exact he.symm

end PoincareConjecture.M25.Topology3D
