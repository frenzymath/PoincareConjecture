import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityOddGraph
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityReflectedTests










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology SchwartzMap LineDeriv

namespace PoincareConjecture.M65Boundary

private theorem equation_half_preimage (R : ℝ) :
    boundaryPlaneReflection ⁻¹' (ball (0 : LoopPlane) R ∩ {z | 0 < z 1}) =
      ball (0 : LoopPlane) R ∩ {z | z 1 < 0} := by
  ext z
  simp only [mem_preimage, mem_inter_iff, mem_ball_zero_iff, mem_ofPred_eq,
    LinearIsometryEquiv.norm_map, (reflection_coordinates _).2, neg_pos]

private theorem equation_half_cover (R : ℝ) :
    let U := ball (0 : LoopPlane) R ∩ {z | 0 < z 1}
    Disjoint U (boundaryPlaneReflection ⁻¹' U) ∧
      (U ∪ boundaryPlaneReflection ⁻¹' U : Set LoopPlane) =ᵐ[volume] ball (0 : LoopPlane) R := by
  dsimp only []
  rw [equation_half_preimage]
  refine ⟨Set.disjoint_left.mpr (fun z hu hl =>
    (not_lt_of_ge (show 0 < z 1 from hu.2).le) (show z 1 < 0 from hl.2)), ?_⟩
  have hnull : volume {z : LoopPlane | z 1 = 0} = 0 := by
    let L : LoopPlane →L[ℝ] ℝ := EuclideanSpace.proj 1
    change volume (LinearMap.ker L.toLinearMap : Set LoopPlane) = 0
    apply Measure.addHaar_submodule
    intro htop
    have hm : EuclideanSpace.basisFun (Fin 2) ℝ 1 ∈ LinearMap.ker L.toLinearMap := by
      rw [htop]; trivial
    norm_num [L, LinearMap.mem_ker, EuclideanSpace.basisFun_apply] at hm
  have hne : ∀ᵐ z : LoopPlane ∂volume, z 1 ≠ 0 := by
    simpa only [ae_iff, not_not] using hnull
  filter_upwards [hne] with z hz
  apply propext
  change ((z ∈ ball (0 : LoopPlane) R ∧ 0 < z 1) ∨
    (z ∈ ball (0 : LoopPlane) R ∧ z 1 < 0)) ↔ z ∈ ball (0 : LoopPlane) R
  constructor
  · exact fun h => h.elim And.left And.left
  · intro h
    rcases lt_or_gt_of_ne hz with hz | hz
    · exact Or.inr ⟨h, hz⟩
    · exact Or.inl ⟨h, hz⟩

private theorem equation_reflected_integrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {R : ℝ} (f : LoopPlane → E) (c : ℝ)
    (hf : IntegrableOn f (ball (0 : LoopPlane) R ∩ {z | 0 < z 1})) :
    IntegrableOn (fun z => if 0 ≤ z 1 then f z else c • f (boundaryPlaneReflection z))
      (ball (0 : LoopPlane) R) := by
  let U := ball (0 : LoopPlane) R ∩ {z | 0 < z 1}
  let T := boundaryPlaneReflection ⁻¹' U
  have hU : MeasurableSet U := measurableSet_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj 1).continuous).measurableSet
  have hT : MeasurableSet T := hU.preimage boundaryPlaneReflection.continuous.measurable
  have hupper : IntegrableOn
      (fun z => if 0 ≤ z 1 then f z else c • f (boundaryPlaneReflection z)) U := by
    apply hf.congr_fun _ hU
    exact fun z hz => (if_pos (show 0 < z 1 from hz.2).le).symm
  have hlower : IntegrableOn
      (fun z => if 0 ≤ z 1 then f z else c • f (boundaryPlaneReflection z)) T := by
    have hc := (boundaryPlaneReflection.measurePreserving.restrict_preimage_emb
      boundaryPlaneReflection.toHomeomorph.measurableEmbedding U).integrable_comp_of_integrable hf
    have hcs : IntegrableOn (fun z => c • f (boundaryPlaneReflection z)) T := hc.smul c
    apply hcs.congr_fun _ hT
    intro z hz
    have ht : z ∈ ball (0 : LoopPlane) R ∩ {z | z 1 < 0} := by
      simpa only [T, U, equation_half_preimage] using hz
    exact (if_neg (not_le.mpr ht.2)).symm
  exact (hupper.union hlower).congr_set_ae (equation_half_cover R).2.symm

private theorem equation_integral_split {R : ℝ} {f : LoopPlane → ℝ}
    (hf : IntegrableOn f (ball (0 : LoopPlane) R)) :
    (∫ z in ball (0 : LoopPlane) R, f z) =
      ∫ z in ball (0 : LoopPlane) R ∩ {z | 0 < z 1}, f z + f (boundaryPlaneReflection z) := by
  let U := ball (0 : LoopPlane) R ∩ {z | 0 < z 1}
  let T := boundaryPlaneReflection ⁻¹' U
  have hU : MeasurableSet U := measurableSet_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj 1).continuous).measurableSet
  have hT : MeasurableSet T := hU.preimage boundaryPlaneReflection.continuous.measurable
  have hsub : T ⊆ ball (0 : LoopPlane) R := by
    rw [show T = ball (0 : LoopPlane) R ∩ {z | z 1 < 0} from equation_half_preimage R]
    exact inter_subset_left
  have hfirst := hf.mono_set (show U ⊆ ball (0 : LoopPlane) R from inter_subset_left)
  have hsecond : IntegrableOn (fun z => f (boundaryPlaneReflection z)) U := by
    have hc := (boundaryPlaneReflection.measurePreserving.restrict_preimage_emb
      boundaryPlaneReflection.toHomeomorph.measurableEmbedding T).integrable_comp_of_integrable
        (hf.mono_set hsub)
    have he : boundaryPlaneReflection ⁻¹' T = U := by
      ext z
      simp only [T, mem_preimage, reflection_involution]
    change Integrable (fun z => f (boundaryPlaneReflection z)) (volume.restrict U)
    simpa only [he, Function.comp_def] using hc
  rw [← setIntegral_congr_set (equation_half_cover R).2,
    setIntegral_union (equation_half_cover R).1 hT hfirst (hf.mono_set hsub),
    integral_add hfirst hsecond]
  congr 1
  have hc := boundaryPlaneReflection.measurePreserving.setIntegral_preimage_emb
    boundaryPlaneReflection.toHomeomorph.measurableEmbedding
    (fun z => f (boundaryPlaneReflection z)) U
  simpa only [Function.comp_def, reflection_involution] using hc

set_option maxHeartbeats 1200000 in





theorem halfDisk_odd_localMap_equation {N : ℕ} {R : ℝ}
    (D : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin N))
    (Y : M65LocalWeakMap (id : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
      (ball (0 : LoopPlane) R))
    (hY : ∀ i z, Y.derivative i z = if 0 ≤ z 1 then D i z else
      (if i = 0 then (-1 : ℝ) else 1) • D i (boundaryPlaneReflection z))
    (hD : ∀ i, IntegrableOn (D i) (ball (0 : LoopPlane) R ∩ {z | 0 < z 1}))
    (f : Fin N → LoopPlane → ℝ)
    (hf : ∀ j, IntegrableOn (f j) (ball (0 : LoopPlane) R ∩ {z | 0 < z 1}))
    (heq : ∀ j (test : 𝓢(LoopPlane, ℝ)), HasCompactSupport test →
      tsupport test ⊆ ball (0 : LoopPlane) R ∩ {z | 0 < z 1} →
      (∫ z in ball (0 : LoopPlane) R ∩ {z | 0 < z 1},
        ∑ i : Fin 2, D i z j * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
          -(∫ z in ball (0 : LoopPlane) R ∩ {z | 0 < z 1}, f j z * test z)) :
    let g := fun j z => if 0 ≤ z 1 then f j z else -f j (boundaryPlaneReflection z)
    (∀ j, IntegrableOn (g j) (ball (0 : LoopPlane) R)) ∧
      ∀ j (test : 𝓢(LoopPlane, ℝ)), HasCompactSupport test →
        tsupport test ⊆ ball (0 : LoopPlane) R →
        (∫ z in ball (0 : LoopPlane) R,
          ∑ i : Fin 2, Y.derivative i z j *
            fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
          -(∫ z in ball (0 : LoopPlane) R, g j z * test z) := by
  classical
  dsimp only []
  let U := ball (0 : LoopPlane) R ∩ {z | 0 < z 1}
  let B := ball (0 : LoopPlane) R
  let g := fun j z => if 0 ≤ z 1 then f j z else -f j (boundaryPlaneReflection z)
  let basis := EuclideanSpace.basisFun (Fin 2) ℝ
  have hU : MeasurableSet U := measurableSet_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj 1).continuous).measurableSet
  have hg (j : Fin N) : IntegrableOn (g j) B := by
    simpa only [smul_eq_mul, neg_one_mul] using equation_reflected_integrable (f j) (-1) (hf j)
  have hDY (i : Fin 2) : IntegrableOn (Y.derivative i) B := by
    exact (equation_reflected_integrable (D i) (if i = 0 then (-1 : ℝ) else 1)
      (hD i)).congr (ae_of_all _ fun z => (hY i z).symm)
  refine ⟨hg, ?_⟩
  intro j test hc hs
  let tr : 𝓢(LoopPlane, ℝ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    boundaryPlaneReflection.toContinuousLinearEquiv test
  let psi := test - tr
  have htr (z : LoopPlane) : tr z = test (boundaryPlaneReflection z) := rfl
  have htrc : HasCompactSupport tr := hc.comp_homeomorph boundaryPlaneReflection.toHomeomorph
  have htrs : tsupport tr ⊆ B := by
    change tsupport ((test : LoopPlane → ℝ) ∘ boundaryPlaneReflection.toHomeomorph) ⊆ B
    rw [tsupport_comp_eq_preimage]
    intro z hz
    have hm : boundaryPlaneReflection z ∈ B := hs hz
    simpa only [B, mem_ball_zero_iff, LinearIsometryEquiv.norm_map] using hm
  have hpsic : HasCompactSupport psi := hc.sub htrc
  have hpsis : tsupport psi ⊆ B := (tsupport_sub _ _).trans (union_subset hs htrs)
  have hzero (z : LoopPlane) (hz : z 1 = 0) : psi z = 0 := by
    have he : boundaryPlaneReflection z = z := by
      ext i
      fin_cases i
      · exact (reflection_coordinates z).1
      · change (boundaryPlaneReflection z) 1 = z 1
        rw [(reflection_coordinates z).2, hz, neg_zero]
    change test z - test (boundaryPlaneReflection z) = 0
    rw [he, sub_self]
  have hdtr (z : LoopPlane) (i : Fin 2) :
      fderiv ℝ tr z (basis i) =
        (if i = 0 then (1 : ℝ) else -1) *
          fderiv ℝ test (boundaryPlaneReflection z) (basis i) := by
    have he := congrArg (fun L : LoopPlane →L[ℝ] ℝ => L (basis i))
      ((test.differentiableAt.hasFDerivAt.comp z
        boundaryPlaneReflection.toContinuousLinearEquiv.hasFDerivAt).fderiv)
    change fderiv ℝ tr z (basis i) =
      fderiv ℝ test (boundaryPlaneReflection z) (boundaryPlaneReflection (basis i)) at he
    rw [show boundaryPlaneReflection (basis i) =
        (if i = 0 then (1 : ℝ) else -1) • basis i by
      ext k; fin_cases i <;> fin_cases k <;>
        simp [basis, boundaryPlaneReflection, Complex.orthonormalBasisOneI_repr_apply,
          EuclideanSpace.basisFun_apply], map_smul, smul_eq_mul] at he
    exact he
  have hdpsi (z : LoopPlane) (i : Fin 2) : fderiv ℝ psi z (basis i) =
      fderiv ℝ test z (basis i) - (if i = 0 then (1 : ℝ) else -1) *
        fderiv ℝ test (boundaryPlaneReflection z) (basis i) := by
    rw [show fderiv ℝ psi z = fderiv ℝ test z - fderiv ℝ tr z from
      (test.differentiableAt.hasFDerivAt.sub tr.differentiableAt.hasFDerivAt).fderiv,
      sub_apply, hdtr]
  have hw := halfDisk_equation_zero_diameter_test (fun i z => D i z j) (f j)
    (fun i => (hD i).eval_piLp j) (hf j) (heq j) psi hpsic hpsis hzero
  have hL : IntegrableOn (fun z => ∑ i : Fin 2,
      Y.derivative i z j * fderiv ℝ test z (basis i)) B := by
    apply integrable_finsetSum
    intro i _
    exact ((hDY i).eval_piLp j).mul_bdd (∂_{basis i} test).continuous.aestronglyMeasurable
      (ae_of_all _ fun z => (∂_{basis i} test).norm_le_seminorm ℝ z)
  have hF : IntegrableOn (fun z => g j z * test z) B :=
    (hg j).mul_bdd test.continuous.aestronglyMeasurable
      (ae_of_all _ fun z => test.norm_le_seminorm ℝ z)
  rw [equation_integral_split hL, equation_integral_split hF]
  have hleft : (∫ z in U,
      (∑ i : Fin 2, Y.derivative i z j * fderiv ℝ test z (basis i)) +
        ∑ i : Fin 2, Y.derivative i (boundaryPlaneReflection z) j *
          fderiv ℝ test (boundaryPlaneReflection z) (basis i)) =
      ∫ z in U, ∑ i : Fin 2, D i z j * fderiv ℝ psi z (basis i) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hU] with z hz
    have hp : 0 ≤ z 1 := (show 0 < z 1 from hz.2).le
    have hn : ¬0 ≤ (boundaryPlaneReflection z) 1 := by
      rw [(reflection_coordinates _).2]; linarith [show 0 < z 1 from hz.2]
    simp only [hY, if_pos hp, if_neg hn, reflection_involution,
      PiLp.smul_apply, smul_eq_mul, hdpsi, Fin.sum_univ_two]
    norm_num
    ring
  have hright : (∫ z in U, g j z * test z +
      g j (boundaryPlaneReflection z) * test (boundaryPlaneReflection z)) =
        ∫ z in U, f j z * psi z := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hU] with z hz
    have hp : 0 ≤ z 1 := (show 0 < z 1 from hz.2).le
    have hn : ¬0 ≤ (boundaryPlaneReflection z) 1 := by
      rw [(reflection_coordinates _).2]; linarith [show 0 < z 1 from hz.2]
    simp only [g, if_pos hp, if_neg hn, reflection_involution, psi, sub_apply, htr]
    ring
  rw [hleft, hright]
  exact hw




theorem halfDisk_odd_localMap_growth {N : ℕ} {R C : ℝ}
    (D : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin N))
    (Y : M65LocalWeakMap (id : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
      (ball (0 : LoopPlane) R))
    (hY : ∀ i z, Y.derivative i z = if 0 ≤ z 1 then D i z else
      (if i = 0 then (-1 : ℝ) else 1) • D i (boundaryPlaneReflection z))
    (f : Fin N → LoopPlane → ℝ)
    (hgrowth : ∀ j, ∀ᵐ z ∂volume.restrict (ball (0 : LoopPlane) R ∩ {z | 0 < z 1}),
      |f j z| ≤ C * ∑ k : Fin N, ∑ i : Fin 2, (D i z k) ^ 2) :
    ∀ j, ∀ᵐ z ∂volume.restrict (ball (0 : LoopPlane) R),
      |if 0 ≤ z 1 then f j z else -f j (boundaryPlaneReflection z)| ≤
        C * ∑ k : Fin N, ∑ i : Fin 2, (Y.derivative i z k) ^ 2 := by
  intro j
  let U := ball (0 : LoopPlane) R ∩ {z | 0 < z 1}
  have hU : MeasurableSet U := measurableSet_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj 1).continuous).measurableSet
  have hG := (ae_restrict_iff' hU).mp (hgrowth j)
  have hR := boundaryPlaneReflection.measurePreserving.quasiMeasurePreserving.ae hG
  filter_upwards [ae_restrict_of_ae hG, ae_restrict_of_ae hR,
    ae_restrict_of_ae (equation_half_cover R).2, ae_restrict_mem measurableSet_ball]
      with z hz hr he hb
  have hmem : z ∈ U ∪ boundaryPlaneReflection ⁻¹' U := by
    change (z ∈ U ∪ boundaryPlaneReflection ⁻¹' U) = (z ∈ ball (0 : LoopPlane) R) at he
    rw [he]; exact hb
  rcases hmem with hp | hn
  · have hpos : 0 ≤ z 1 := (show 0 < z 1 from hp.2).le
    simpa only [hY, if_pos hpos] using hz hp
  · have hneg : ¬0 ≤ z 1 := by
      have hh : 0 < (boundaryPlaneReflection z) 1 := hn.2
      rw [(reflection_coordinates _).2] at hh
      linarith
    have hs : (∑ k : Fin N, ∑ i : Fin 2, (Y.derivative i z k) ^ 2) =
        ∑ k : Fin N, ∑ i : Fin 2, (D i (boundaryPlaneReflection z) k) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      rw [hY, if_neg hneg]
      by_cases hi : i = 0 <;> simp [hi]
    rw [if_neg hneg, abs_neg, hs]
    exact hr hn

end PoincareConjecture.M65Boundary
