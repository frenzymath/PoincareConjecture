import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ScalarHeightCompression
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HorizontalTimeFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightPlaneProjection











set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff NNReal Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

local notation "D1" => Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞
local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞






theorem exists_compact_ambient_height_compression
    (u : UnitTwoSphere) (c : ℝ)
    {Q : Set E3} (hQ : IsCompact Q)
    {J : Set ℝ} (hJ : IsCompact J) (hcJ : c ∉ J)
    {ε : ℝ} (hε : 0 < ε) :
    let H : E3 → ℝ := fun y => ⟪(u : E3), y⟫_ℝ
    let P : E3 → E2 := fun y => (heightPlaneCoordinates u y).1
    ∃ (h : D1) (G0 G : D3) (I : ℝ → D3) (k δ a : ℝ) (C : Set E3),
      0 < k ∧ k ≤ 1 / 2 ∧ 0 < δ ∧ 0 < a ∧
      (∀ y ∈ Q, ‖P y‖ < a) ∧ StrictMono (fun z => h z) ∧
      (∀ᶠ z in 𝓝ˢ J, h z = c + k * (z - c)) ∧
      (∀ z, |z - c| ≤ δ → h z = z) ∧
      (∀ y, H (G0 y) = h (H y) ∧ P (G0 y) = P y) ∧
      (∀ y, ‖P y‖ ≤ a → G y = G0 y ∧ G.symm y = G0.symm y) ∧
      (∀ y, |H y - c| ≤ δ → G0 y = y ∧ ∀ s : ℝ, I s y = y) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E3 => I p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E3 => (I p.1).symm p.2) ∧
      (∀ y, I 0 y = y) ∧ I 1 = G ∧
      (∀ (s : ℝ) (y : E3), (I s).symm y = I (-s) y) ∧
      (∀ (s : ℝ) (y : E3), P (I s y) = P y) ∧
      IsCompact C ∧ (∀ s : ℝ, tsupport (fun y => I s y - y) ⊆ C) ∧
      ∀ y ∈ Q, |H (G y) - c| < ε := by
  let A := heightPlaneCoordinates u
  let H : E3 → ℝ := fun y => ⟪(u : E3), y⟫_ℝ
  let P : E3 → E2 := fun y => (A y).1
  have hH (y : E3) : H y = (A y).2 := (heightPlaneCoordinates_snd u y).symm
  have hcoord (y : E3) : A y = (P y, H y) := Prod.ext rfl (hH y).symm
  have hrec (y : E3) : A.symm (P y, H y) = y := by
    rw [← hcoord, A.symm_apply_apply]
  have hHcont : Continuous H := by
    simpa only [H, A, heightPlaneCoordinates_snd] using A.continuous.snd
  have hPcont : Continuous P := A.continuous.fst
  obtain ⟨R, hR, hheight⟩ :=
    (hJ.union (hQ.image hHcont)).isBounded.subset_ball_lt (1 : ℝ) c
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  obtain ⟨ρ, hρ, hρJ⟩ :=
    Metric.mem_nhds_iff.mp (hJ.isClosed.isOpen_compl.mem_nhds hcJ)
  let d := min (ρ / 2) (1 / 2 : ℝ)
  let k := min (1 / 2 : ℝ) (ε / (2 * R))
  have hd : 0 < d := by dsimp [d]; positivity
  have hdR : d ≤ R := (min_le_right _ _).trans (by linarith)
  have hk : 0 < k := by dsimp [k]; positivity
  have hkhalf : k ≤ 1 / 2 := min_le_left _ _
  have hk1 : k ≤ 1 := hkhalf.trans (by norm_num)
  have hkR : k * R < ε := by
    have hmul : k * (2 * R) ≤ ε :=
      (le_div_iff₀ (by positivity : 0 < 2 * R)).mp (min_le_right _ _)
    nlinarith
  obtain ⟨v, hv, hvc, K, B, hK, hB, T, δ, _, hδ, hfix, haff, hbound⟩ :=
    exists_scalar_height_compression c d R k hd hdR hk hk1
  let h : D1 := boundedFlowDiffeomorph v hK hB hv hvc T
  have hJlower (z : ℝ) (hz : z ∈ J) : d < |z - c| := by
    have hdist : ρ ≤ |z - c| := by
      apply le_of_not_gt
      intro hlt
      exact hρJ (by simpa only [mem_ball, Real.dist_eq] using hlt) hz
    exact (lt_of_le_of_lt (min_le_left _ _) (by linarith : ρ / 2 < ρ)).trans_le hdist
  have hJupper (z : ℝ) (hz : z ∈ J) : |z - c| < R := by
    simpa only [mem_ball, Real.dist_eq] using hheight (Or.inl hz)
  have hQheight (y : E3) (hy : y ∈ Q) : |H y - c| < R := by
    simpa only [mem_ball, Real.dist_eq] using hheight (Or.inr ⟨y, hy, rfl⟩)
  let W : Set ℝ := {z | d < |z - c| ∧ |z - c| < R}
  have habs : Continuous (fun z : ℝ => |z - c|) :=
    (continuous_id.sub continuous_const).abs
  have hW : IsOpen W :=
    (isOpen_lt continuous_const habs).inter (isOpen_lt habs continuous_const)
  have hJW : J ⊆ W := fun z hz => ⟨hJlower z hz, hJupper z hz⟩
  have hnear : ∀ᶠ z in 𝓝ˢ J, h z = c + k * (z - c) := by
    filter_upwards [hW.mem_nhdsSet.mpr hJW] with z hz
    exact haff z hz.1.le hz.2.le
  obtain ⟨a, ha, hplan⟩ := (hQ.image hPcont).isBounded.subset_ball_lt (1 : ℝ) (0 : E2)
  have hapos : 0 < a := lt_trans zero_lt_one ha
  have hpQ (y : E3) (hy : y ∈ Q) : ‖P y‖ < a := by
    simpa only [mem_ball, dist_zero_right] using hplan ⟨y, hy, rfl⟩
  have hcut : closedBall (0 : E2) a ⊆ ball 0 (a + 1) := by
    intro x hx
    exact mem_ball.mpr ((mem_closedBall.mp hx).trans_lt (lt_add_one a))
  obtain ⟨χ, hχ, hχc, _, hχnear, _⟩ :=
    exists_compact_smooth_cutoff (isCompact_closedBall (0 : E2) a) isOpen_ball hcut
  have hχone (x : E2) (hx : ‖x‖ ≤ a) : χ x = 1 :=
    subset_of_mem_nhdsSet hχnear (by simpa only [mem_closedBall, dist_zero_right] using hx)
  let D := A.toDiffeomorph
  let F (t : ℝ) := horizontalTimeFlowDiffeomorph v hK hB hv hvc χ hχ t
  let F0 := horizontalTimeFlowDiffeomorph v hK hB hv hvc (fun _ : E2 => 1)
    contDiff_const T
  let G0 : D3 := D.trans (F0.trans D.symm)
  let I (s : ℝ) : D3 := D.trans ((F (s * T)).trans D.symm)
  let G : D3 := I 1
  have hG0 (y : E3) : G0 y = A.symm (P y, boundedFlow v hK hB (H y) T) := by
    change A.symm ((A y).1, boundedFlow v hK hB (A y).2 (1 * T)) = _
    rw [one_mul, ← hH]
  have hG0inv (y : E3) :
      G0.symm y = A.symm (P y, boundedFlow v hK hB (H y) (-T)) := by
    change A.symm ((A y).1, boundedFlow v hK hB (A y).2 (1 * (-T))) = _
    rw [one_mul, ← hH]
  have hI (s : ℝ) (y : E3) :
      I s y = A.symm (P y, boundedFlow v hK hB (H y) (χ (P y) * (s * T))) := by
    change A.symm ((A y).1, boundedFlow v hK hB (A y).2 (χ (A y).1 * (s * T))) = _
    rw [← hH]
  have hIinv (s : ℝ) (y : E3) :
      (I s).symm y =
        A.symm (P y, boundedFlow v hK hB (H y) (χ (P y) * (-(s * T)))) := by
    change A.symm ((A y).1, boundedFlow v hK hB (A y).2 (χ (A y).1 * (-(s * T)))) = _
    rw [← hH]
  have hIneg (s : ℝ) (y : E3) : (I s).symm y = I (-s) y := by
    simp only [hIinv, hI, neg_mul]
  have hIsmooth : ContDiff ℝ ∞ (fun p : ℝ × E3 => I p.1 p.2) :=
    A.symm.contDiff.comp ((horizontalTimeFlowDiffeomorph_contDiff v hK hB hv hvc χ hχ).comp
      ((contDiff_fst.mul contDiff_const).prodMk (A.contDiff.comp contDiff_snd)))
  have hIinverse : ContDiff ℝ ∞ (fun p : ℝ × E3 => (I p.1).symm p.2) := by
    simpa only [hIneg, Function.comp_def, Pi.neg_apply] using
      hIsmooth.comp (contDiff_fst.neg.prodMk contDiff_snd)
  have hIzero (y : E3) : I 0 y = y := by
    rw [hI, zero_mul, mul_zero, boundedFlow_zero, hrec]
  have hIp (s : ℝ) (y : E3) : P (I s y) = P y := by
    rw [hI]
    change (A (A.symm _)).1 = P y
    rw [A.apply_symm_apply]
  have hG0laws (y : E3) : H (G0 y) = h (H y) ∧ P (G0 y) = P y := by
    constructor
    · rw [hH, hG0, A.apply_symm_apply]
      rfl
    · rw [hG0]
      change (A (A.symm _)).1 = P y
      rw [A.apply_symm_apply]
  have hcylinder (y : E3) (hy : ‖P y‖ ≤ a) : G y = G0 y ∧ G.symm y = G0.symm y := by
    change I 1 y = G0 y ∧ (I 1).symm y = G0.symm y
    constructor <;> simp only [hI, hIinv, hG0, hG0inv, hχone (P y) hy, one_mul]
  have hcentral (y : E3) (hy : |H y - c| ≤ δ) : G0 y = y ∧ ∀ s : ℝ, I s y = y := by
    constructor
    · rw [hG0, hfix T (H y) hy, hrec]
    · intro s
      rw [hI, hfix _ (H y) hy, hrec]
  let C : Set E3 := A.symm '' (tsupport χ ×ˢ tsupport v)
  have hC : IsCompact C := (hχc.prod hvc).image A.symm.continuous
  have hsupport (s : ℝ) : tsupport (fun y => I s y - y) ⊆ C := by
    apply closure_minimal ?_ hC.isClosed
    intro y hy
    have hne : F (s * T) (A y) ≠ A y := by
      intro heq
      apply hy
      apply sub_eq_zero.mpr
      change A.symm (F (s * T) (A y)) = y
      rw [heq, A.symm_apply_apply]
    have hprod : A y ∈ tsupport χ ×ˢ tsupport v :=
      horizontalTimeFlowDiffeomorph_tsupport_subset v hK hB hv hvc χ hχ (s * T)
        (subset_tsupport _ (sub_ne_zero.mpr hne))
    exact ⟨A y, hprod, A.symm_apply_apply y⟩
  refine ⟨h, G0, G, I, k, δ, a, C, hk, hkhalf, hδ, hapos, hpQ,
    boundedFlow_strictMono v hK hB hv hvc T, hnear, fun z hz => hfix T z hz,
    hG0laws, hcylinder, hcentral, hIsmooth, hIinverse, hIzero, rfl, hIneg,
    hIp, hC, hsupport, ?_⟩
  intro y hy
  change |H (G y) - c| < ε
  rw [(hcylinder y (hpQ y hy).le).1, (hG0laws y).1]
  exact (hbound (H y) (hQheight y hy).le).trans_lt hkR

end PoincareConjecture.M25.Topology3D
