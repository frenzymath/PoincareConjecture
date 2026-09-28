import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsEndLabels
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsCanonicalNormalization
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereNormalSign

set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

local notation "P" => (ℝ × E2)

theorem exists_stackCapEndFamily
    {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (C : SurgeryCapTag psi u)
    (c : ℝ → UnitCircle → E2) (c0 c1 jL jR : ℝ)
    (hP : PlanarSchoenfliesService) (hc01 : c0 < c1)
    (hc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
      (fun p : ℝ × UnitCircle => c p.1 p.2))
    (hce : ∀ z ∈ Icc c0 c1, IsPlanarEmbedding (c z))
    (hJband : Ioo jL jR ⊆ Icc c0 c1)
    (hJcap : Ioo jL jR ⊆
      Ioo (C.cutHeight + C.sign * C.removal - C.scale * C.overlapWidth / 2)
        (C.cutHeight + C.sign * C.removal + C.scale * C.overlapWidth / 2))
    (hfull : ∀ z ∈ Ioo jL jR,
      range (c z) = {x : E2 |
        (heightPlaneCoordinates u).symm (x,z) ∈
          range (fun q : UnitTwoSphere => psi (q,0))})
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
    (∀ z ∉ Ioo jL jR, ∀ q, cbar z q = c z q) ∧
    ∃ D : PlanarSchoenfliesFamilyData cbar c0 c1,
      ∃ G : PlanarFamilyGraphChart D,
        let T := stackCapEndChart C R
        let E := T.trans G.chart.symm
        let g := fun p : P => (E p).2
        (∀ z ∈ Icc A B, ∀ q ∈ sphere (0 : E2) 1,
          T (z,q) = G.chart (z,q)) ∧
        (∀ z ∈ Icc A B, ∃ N : BallNeighborhoodChart E2 E2,
          ∀ q ∈ sphere (0 : E2) 1,
            (fun y => N.chart y) =ᶠ[𝓝 q] (fun y => (T (z,y)).2)) ∧
        IsOpen E.source ∧ ContDiffOn ℝ ∞ g E.source ∧
        Icc A B ×ˢ sphere (0 : E2) 1 ⊆ E.source ∧
        (∀ z ∈ Icc A B, ∀ q ∈ sphere (0 : E2) 1, g (z,q) = q) ∧
        (∀ z ∈ Icc A B, ∀ q ∈ sphere (0 : E2) 1,
          0 < ⟪q, fderiv ℝ (fun y => g (z,y)) q q⟫_ℝ) := by
  classical
  let : Fact (Module.finrank ℝ E2 = 1 + 1) := ⟨by simp [E2]⟩
  obtain ⟨D0⟩ := hP.2 c0 c1 c hc01 hc hce
  obtain ⟨G0⟩ := D0.nonempty_graphChart hc01
  have hJ : jL < jR := (hLA.trans_le hAB).trans hBR
  obtain ⟨phi, hphi, _hphii, hlabels, _hphiout⟩ :=
    exists_stackCapEndLabels C c c0 c1 jL jR D0 G0 hJ hJband hJcap hfull
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
  let T := stackCapEndChart C R
  let E := T.trans G.chart.symm
  let g := fun p : P => (E p).2
  have hTs := stackCapEndChart_spec C R
  have hTf := stackCapEndFiber_spec C R
  have hband (z : ℝ) (hz : z ∈ Icc A B) : z ∈ Ioo jL jR :=
    (Icc_subset_Ioo_iff hAB).mpr ⟨hLA, hBR⟩ hz
  have hGsource (z : ℝ) (hz : z ∈ Icc A B) (q : E2)
      (hq : q ∈ sphere (0 : E2) 1) : (z, q) ∈ G.chart.source :=
    G.mem_source (hJband (hband z hz))
      (mem_ball_zero_iff.mpr ((mem_sphere_zero_iff_norm.mp hq).trans_lt G.one_lt_radius))
  have hTsource (z : ℝ) (q : E2) (hq : q ∈ sphere (0 : E2) 1) : (z, q) ∈ T.source :=
    hTs.2.2.2.2.2.2.1 ⟨mem_univ _, sphere_subset_closedBall hq⟩
  have hmatch (z : ℝ) (hz : z ∈ Icc A B) (q : E2)
      (hq : q ∈ sphere (0 : E2) 1) : T (z, q) = G.chart (z, q) := by
    let q' : UnitCircle := ⟨R q, by simpa only [mem_sphere_zero_iff_norm, R.norm_map] using hq⟩
    have he : cbar z ⟨q, hq⟩ = (T (z, q)).2 := by
      change c z (L z ⟨q, hq⟩) = _
      rw [hLagree z hz]
      exact (hlabels z (hband z hz) q').2.2
    apply Prod.ext
    · rw [G.chart_apply]
      exact hTs.2.2.2.2.2.2.2.1 _ (hTsource z q hq)
    · rw [G.chart_apply, D.chart_boundary z (hJband (hband z hz)) ⟨q, hq⟩]
      exact he.symm
  have hEsource : Icc A B ×ˢ sphere (0 : E2) 1 ⊆ E.source := by
    intro p hp
    refine ⟨hTsource p.1 p.2 hp.2, ?_⟩
    change T p ∈ G.chart.target
    rw [hmatch p.1 hp.1 p.2 hp.2]
    exact G.chart.map_source (hGsource p.1 hp.1 p.2 hp.2)
  have hEsmooth : ContDiffOn ℝ ∞ E E.source :=
    G.smooth_symm.comp (hTs.2.2.2.2.1.mono inter_subset_left) (fun _ hp => hp.2)
  have hfixed (z : ℝ) (hz : z ∈ Icc A B) (q : E2)
      (hq : q ∈ sphere (0 : E2) 1) : g (z, q) = q := by
    change (G.chart.symm (T (z, q))).2 = q
    rw [hmatch z hz q hq, G.chart.left_inv (hGsource z hz q hq)]
  refine ⟨R, hR, cbar, hcb, hcbe, hrange, hout, D, G, hmatch, ?_,
    E.open_source, hEsmooth.snd, hEsource, hfixed, ?_⟩
  · intro z _hz
    exact ⟨stackCapEndFiber C R z, (hTf.1 z).2.2.2.2⟩
  · intro z hz q hq
    let N := stackCapEndFiber C R z
    let B' := G.fiberBallNeighborhood z (hJband (hband z hz))
    have hN := hTf.1 z
    have hNsource (x : E2) (hx : x ∈ N.chart.source) : (z, x) ∈ T.source := by
      rw [hN.1] at hx
      exact hx
    have hcoord (x : E2) (hx : x ∈ N.chart.source) : (z, N.chart x) = T (z, x) := by
      apply Prod.ext
      · exact (hTs.2.2.2.2.2.2.2.1 _ (hNsource x hx)).symm
      · exact (hN.2.2.1 x)
    have hboundary (x : E2) (hx : x ∈ sphere (0 : E2) 1) : N.chart x = B'.chart x := by
      rw [hN.2.2.1 x, hmatch z hz x hx, G.chart_apply]
      rfl
    have hinside : N.inside = B'.inside := N.inside_eq_of_boundary_eq B'
      (Module.one_lt_rank_of_one_lt_finrank (by simp [E2])) (image_congr hboundary)
    let Q := N.chart.trans B'.chart.symm
    have hQsmooth : ContDiffOn ℝ ∞ Q Q.source :=
      B'.smooth_symm.comp (N.smooth.mono inter_subset_left) (fun _ hp => hp.2)
    have hQinverse : ContDiffOn ℝ ∞ Q.symm Q.target :=
      N.smooth_symm.comp (B'.smooth.mono inter_subset_left) (fun _ hp => hp.2)
    have hqN : q ∈ N.chart.source := N.closedBall_subset_source (sphere_subset_closedBall hq)
    have hqB : q ∈ B'.chart.source := B'.closedBall_subset_source (sphere_subset_closedBall hq)
    have hqQ : q ∈ Q.source := by
      refine ⟨hqN, ?_⟩
      change N.chart q ∈ B'.chart.target
      rw [hboundary q hq]
      exact B'.chart.map_source hqB
    have hlocal : (fun x => g (z, x)) =ᶠ[𝓝 q] (Q : E2 → E2) := by
      filter_upwards [N.chart.open_source.mem_nhds hqN] with x hx
      change (G.chart.symm (T (z, x))).2 = (G.chart.symm (z, N.chart x)).2
      rw [hcoord x hx]
    obtain ⟨J, hJ⟩ := exists_smoothChart_derivative Q hQsmooth hQinverse hqQ
    have hder : DifferentiableAt ℝ (fun x => g (z, x)) q :=
      hJ.differentiableAt.congr_of_eventuallyEq hlocal
    have hinj : Injective (fderiv ℝ (fun x => g (z, x)) q) := by
      rw [hlocal.fderiv_eq, hJ.fderiv]
      exact J.injective
    apply fderiv_normal_pos_of_local_exterior (fun x => g (z, x))
      (mem_sphere_zero_iff_norm.mp hq) hder
      (Eventually.of_forall (fun x hx => hfixed z hz x (mem_sphere_zero_iff_norm.mpr hx))) hinj
    filter_upwards [Q.open_source.mem_nhds hqQ, hlocal] with x hx hxe
    intro hxnorm
    rw [hxe]
    by_contra hnot
    have hsmall : Q x ∈ ball (0 : E2) 1 := mem_ball_zero_iff.mpr (lt_of_not_ge hnot)
    have hNx : N.chart x ∈ B'.inside := by
      refine ⟨Q x, hsmall, ?_⟩
      exact B'.chart.right_inv hx.2
    rw [← hinside] at hNx
    obtain ⟨v, hv, he⟩ := hNx
    have hvx : v = x := N.chart.injOn
      (N.closedBall_subset_source (ball_subset_closedBall hv)) hx.1 he
    rw [hvx] at hv
    exact (not_lt_of_ge hxnorm) (mem_ball_zero_iff.mp hv)

theorem stackCanonicalEndpoint_capEndChart
    {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (C : SurgeryCapTag psi u) (R : E2 ≃ₗᵢ[ℝ] E2)
    (rFlat rOne v0 v1 lambda : ℝ)
    (hrFlat : 0 < rFlat) (hradii : rFlat < rOne) (hrOne : rOne < 1)
    (hv0 : 0 < v0) (hv01 : v0 < v1) (hv1 : v1 < 1)
    (hgap : v1 ^ 2 + rOne ^ 2 < 1) (hlambda : 0 < lambda) :
    let a := stackCanonicalHorizontal v0 v1
    let b := stackCanonicalVertical rFlat rOne
    let M := stackCapProfilePath a a b b 0
    let coord := fun q : UnitTwoSphere => heightCoordinates (q : E3)
    let H := fun y : E3 =>
      ((heightPlaneCoordinates u y).2, (heightPlaneCoordinates u y).1)
    let Qminus := {q : UnitTwoSphere | (coord q).2 ≤ 0}
    let s := C.cutHeight + C.sign * C.removal
    let h := fun q : UnitTwoSphere => s + C.sign * lambda * (M (coord q)).2
    let ep := stackCapCanonicalEndpoint C rFlat rOne v0 v1 lambda
    let T := stackCapEndChart C R
    (∀ q ∈ Qminus, (h q, (M (coord q)).1) ∈ T.source) ∧
    (∀ q ∈ Qminus, ∃ qR ∈ Qminus,
      coord qR = (R (coord q).1, (coord q).2) ∧
        H (ep qR) = T (h q, (M (coord q)).1)) ∧
    H '' (ep '' Qminus) =
      (fun q => T (h q, (M (coord q)).1)) '' Qminus ∧
    (∀ q ∈ Qminus,
      |⟪(u : E3), ep q⟫_ℝ - s| ≤ lambda ∧
      -lambda ≤ C.sign * (⟪(u : E3), ep q⟫_ℝ - s) ∧
      C.sign * (⟪(u : E3), ep q⟫_ℝ - s) ≤ 0) := by
  let a := stackCanonicalHorizontal v0 v1
  let b := stackCanonicalVertical rFlat rOne
  let M := stackCapProfilePath a a b b 0
  let coord := fun q : UnitTwoSphere => heightCoordinates (q : E3)
  let H := fun y : E3 =>
    ((heightPlaneCoordinates u y).2, (heightPlaneCoordinates u y).1)
  let Qminus := {q : UnitTwoSphere | (coord q).2 ≤ 0}
  let s := C.cutHeight + C.sign * C.removal
  let h := fun q : UnitTwoSphere => s + C.sign * lambda * (M (coord q)).2
  let ep := stackCapCanonicalEndpoint C rFlat rOne v0 v1 lambda
  let T := stackCapEndChart C R
  have hM (p : E2 × ℝ) : M p = (a p.2 • p.1, b (a p.2 • p.1) * p.2) := by
    simp only [M, stackCapProfilePath, stackProfileBlend_of_nonpos a a 0 le_rfl,
      stackProfileBlend_of_nonpos b b 0 le_rfl]
  have hbR (S : E2 ≃ₗᵢ[ℝ] E2) (x : E2) : b (S x) = b x := by
    simp only [b, stackCanonicalVertical, S.norm_map]
  have hMR (S : E2 ≃ₗᵢ[ℝ] E2) (p : E2 × ℝ) :
      M (S p.1, p.2) = (S (M p).1, (M p).2) := by
    rw [hM, hM]
    simp only [← S.map_smul, hbR]
  let rot (S : E2 ≃ₗᵢ[ℝ] E2) (q : UnitTwoSphere) : UnitTwoSphere :=
    ⟨heightCoordinates.symm (S (coord q).1, (coord q).2), by
      apply mem_sphere_zero_iff_norm.mpr
      have hn := heightCoordinates_symm_norm_sq (S (coord q).1, (coord q).2)
      rw [S.norm_map] at hn
      have hq := sphere_height_coordinates_sq q
      change ‖(coord q).1‖ ^ 2 + (coord q).2 ^ 2 = 1 at hq
      nlinarith [norm_nonneg (heightCoordinates.symm (S (coord q).1, (coord q).2))]⟩
  have hrot (S : E2 ≃ₗᵢ[ℝ] E2) (q : UnitTwoSphere) :
      coord (rot S q) = (S (coord q).1, (coord q).2) :=
    heightCoordinates.apply_symm_apply _
  have hrotmem (S : E2 ≃ₗᵢ[ℝ] E2) (q : UnitTwoSphere) (hq : q ∈ Qminus) :
      rot S q ∈ Qminus := by
    change (coord (rot S q)).2 ≤ 0
    rw [hrot]
    exact hq
  have hrotinv (q : UnitTwoSphere) : rot R (rot R.symm q) = q := by
    apply Subtype.ext
    apply heightCoordinates.injective
    change coord (rot R (rot R.symm q)) = coord q
    rw [hrot, hrot, R.apply_symm_apply]
  have hTs := stackCapEndChart_spec C R
  have hpoint (q : UnitTwoSphere) :
      H (ep (rot R q)) = T (h q, (M (coord q)).1) := by
    change H (C.tube ((M (coord (rot R q))).1,
      C.cutHeight + C.sign * (C.removal + lambda * (M (coord (rot R q))).2))) = _
    rw [hrot, hMR]
    change H (C.tube (R (M (coord q)).1,
      C.cutHeight + C.sign * (C.removal + lambda * (M (coord q)).2))) =
        H (C.tube (R (M (coord q)).1, h q))
    have hh : C.cutHeight + C.sign * (C.removal + lambda * (M (coord q)).2) = h q := by
      dsimp [h, s]
      ring
    rw [hh]
  have hgeometry (q : UnitTwoSphere) (hq : q ∈ Qminus) :
      ‖(M (coord q)).1‖ ≤ 1 ∧ -1 ≤ (M (coord q)).2 ∧ (M (coord q)).2 ≤ 0 := by
    have hg := stackCanonicalModel_southern_geometry rFlat rOne v0 v1
      hrFlat hradii hrOne hv0 hv01 hv1 hgap (coord q) (sphere_height_coordinates_sq q) hq
    exact ⟨hg.2.1, hg.2.2.1, hg.2.2.2.1⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q hq
    exact hTs.2.2.2.2.2.2.1 ⟨mem_univ _, mem_closedBall_zero_iff.mpr (hgeometry q hq).1⟩
  · intro q hq
    exact ⟨rot R q, hrotmem R q hq, hrot R q, hpoint q⟩
  · apply Subset.antisymm
    · rintro y ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      refine ⟨rot R.symm q, hrotmem R.symm q hq, ?_⟩
      change T (h (rot R.symm q), (M (coord (rot R.symm q))).1) = H (ep q)
      rw [← hpoint, hrotinv]
    · rintro y ⟨q, hq, rfl⟩
      exact ⟨ep (rot R q), ⟨rot R q, hrotmem R q hq, rfl⟩, hpoint q⟩
  · intro q hq
    have hg := hgeometry q hq
    have hs : ((M (coord q)).1,
        C.cutHeight + C.sign * (C.removal + lambda * (M (coord q)).2)) ∈ C.tube.source :=
      C.tube_source ⟨mem_closedBall_zero_iff.mpr hg.1, mem_univ _⟩
    have hh : ⟪(u : E3), ep q⟫_ℝ - s = C.sign * lambda * (M (coord q)).2 := by
      change ⟪(u : E3), C.tube ((M (coord q)).1,
        C.cutHeight + C.sign * (C.removal + lambda * (M (coord q)).2))⟫_ℝ - s = _
      rw [C.tube_height _ hs]
      dsimp [s]
      ring
    have hsq : C.sign ^ 2 = 1 := by nlinarith [sq_abs C.sign, C.sign_abs]
    have hsigned : C.sign * (⟪(u : E3), ep q⟫_ℝ - s) = lambda * (M (coord q)).2 := by
      rw [hh]
      calc
        C.sign * (C.sign * lambda * (M (coord q)).2) =
            C.sign ^ 2 * (lambda * (M (coord q)).2) := by ring
        _ = lambda * (M (coord q)).2 := by rw [hsq, one_mul]
    refine ⟨?_, ?_, ?_⟩
    · rw [hh, abs_mul, abs_mul, C.sign_abs, abs_of_pos hlambda, one_mul]
      have habs : |(M (coord q)).2| ≤ 1 := abs_le.mpr ⟨hg.2.1, hg.2.2.trans zero_le_one⟩
      nlinarith
    · rw [hsigned]
      nlinarith [mul_nonneg hlambda.le (show 0 ≤ (M (coord q)).2 + 1 by linarith)]
    · rw [hsigned]
      exact mul_nonpos_of_nonneg_of_nonpos hlambda.le hg.2.2

end PoincareConjecture.M25.Topology3D
