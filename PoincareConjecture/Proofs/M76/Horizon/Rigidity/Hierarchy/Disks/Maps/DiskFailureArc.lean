import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Maps.SourceDiskNormalForm
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.FoldedFailureArc

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

private instance : Fact (0 < p) := ⟨by norm_num⟩

theorem exists_unit_square_proper_PL_arc
    (x y : V2) (hx : x ∈ Q) (hy : y ∈ Q) (hne : x ≠ y) :
    ∃ (param : ℝ → V2) (k : C(unitInterval, V2)),
      FinitePiecewiseAffineOn param (Icc (0 : ℝ) 1) ∧
      (∀ t : unitInterval, param t = k t) ∧ Topology.IsEmbedding k ∧
      k 0 = x ∧ k 1 = y ∧ range k ⊆ D ∧
      (∀ t, k t ∈ Q ↔ t = 0 ∨ t = 1) := by
  have hxnorm : ‖x‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx
  have hynorm : ‖y‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hy
  let param : ℝ → V2 := fun t => max (1 - 2 * t) 0 • x + max (2 * t - 1) 0 • y
  have hleft (t : ℝ) (ht : t ≤ 1 / 2) : param t = (1 - 2 * t) • x := by
    simp only [param, max_eq_left (by linarith : 0 ≤ 1 - 2 * t),
      max_eq_right (by linarith : 2 * t - 1 ≤ 0), zero_smul, add_zero]
  have hright (t : ℝ) (ht : 1 / 2 ≤ t) : param t = (2 * t - 1) • y := by
    simp only [param, max_eq_right (by linarith : 1 - 2 * t ≤ 0),
      max_eq_left (by linarith : 0 ≤ 2 * t - 1), zero_smul, zero_add]
  have hnorm (t : ℝ) : ‖param t‖ = |1 - 2 * t| := by
    rcases le_total t (1 / 2) with ht | ht
    · rw [hleft t ht, norm_smul, hxnorm, mul_one, Real.norm_eq_abs]
    · rw [hright t ht, norm_smul, hynorm, mul_one, Real.norm_eq_abs]
      have hh : 2 * t - 1 = -(1 - 2 * t) := by ring
      rw [hh, abs_neg]
  have hinj : Function.Injective param := by
    intro s t hst
    have hn := congrArg norm hst
    rw [hnorm, hnorm] at hn
    rcases le_total s (1 / 2) with hs | hs <;>
      rcases le_total t (1 / 2) with ht | ht
    · rw [abs_of_nonneg (by linarith : 0 ≤ 1 - 2 * s),
        abs_of_nonneg (by linarith : 0 ≤ 1 - 2 * t)] at hn
      linarith
    · rw [hleft s hs, hright t ht] at hst
      rw [abs_of_nonneg (by linarith : 0 ≤ 1 - 2 * s),
        abs_of_nonpos (by linarith : 1 - 2 * t ≤ 0)] at hn
      by_cases hz : 1 - 2 * s = 0
      · linarith
      · have hcoef : 2 * t - 1 = 1 - 2 * s := by linarith
        rw [hcoef] at hst
        exact False.elim (hne ((smul_right_injective V2 hz) hst))
    · rw [hright s hs, hleft t ht] at hst
      rw [abs_of_nonpos (by linarith : 1 - 2 * s ≤ 0),
        abs_of_nonneg (by linarith : 0 ≤ 1 - 2 * t)] at hn
      by_cases hz : 1 - 2 * t = 0
      · linarith
      · have hcoef : 2 * s - 1 = 1 - 2 * t := by linarith
        rw [hcoef] at hst
        exact False.elim (hne ((smul_right_injective V2 hz) hst).symm)
    · rw [abs_of_nonpos (by linarith : 1 - 2 * s ≤ 0),
        abs_of_nonpos (by linarith : 1 - 2 * t ≤ 0)] at hn
      linarith
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKI, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)
  have hconst (r : ℝ) : FinitePiecewiseAffineOn (fun _ : ℝ => r) (Icc (0 : ℝ) 1) :=
    ⟨K, hK, hKI, K.affineOnFaces_affine (ContinuousAffineMap.const ℝ ℝ r)⟩
  have hid : FinitePiecewiseAffineOn (fun t : ℝ => t) (Icc (0 : ℝ) 1) :=
    ⟨K, hK, hKI, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩
  have htwice : FinitePiecewiseAffineOn (fun t : ℝ => 2 * t) (Icc (0 : ℝ) 1) :=
    hid.postcomp ((2 : ℝ) • ContinuousAffineMap.id ℝ ℝ)
  have hL := (((hconst 1).sub htwice).max (hconst 0)).postcomp
    ((ContinuousLinearMap.id ℝ ℝ).smulRight x).toContinuousAffineMap
  have hU := ((htwice.sub (hconst 1)).max (hconst 0)).postcomp
    ((ContinuousLinearMap.id ℝ ℝ).smulRight y).toContinuousAffineMap
  have hPL : FinitePiecewiseAffineOn param (Icc (0 : ℝ) 1) := hL.add hU
  let k : C(unitInterval, V2) := ⟨fun t => param t, hPL.continuousOn.domRestrict⟩
  refine ⟨param, k, hPL, fun _ => rfl,
    k.continuous.isClosedEmbedding (fun s t hst => Subtype.ext (hinj hst)) |>.isEmbedding,
    ?_, ?_, ?_, ?_⟩
  · change param 0 = x
    rw [hleft 0 (by norm_num)]
    simp
  · change param 1 = y
    rw [hright 1 (by norm_num)]
    norm_num
  · rintro _ ⟨t, rfl⟩
    change dist (param t) 0 ≤ 1
    rw [dist_zero_right, hnorm, abs_le]
    constructor <;> linarith [t.property.1, t.property.2]
  · intro t
    rw [mem_sphere, dist_zero_right]
    change ‖param t‖ = 1 ↔ _
    rw [hnorm, abs_eq (by norm_num : (0 : ℝ) ≤ 1)]
    constructor
    · rintro (ht | ht)
      · exact Or.inl (Subtype.ext (by change (t : ℝ) = 0; linarith))
      · exact Or.inr (Subtype.ext (by change (t : ℝ) = 1; linarith))
    · rintro (rfl | rfl) <;> norm_num

private theorem continuous_short_arc_lift
    (f : C(unitInterval, C0)) {cut a b : ℝ} (ha : cut < a) (hb : b < cut + p)
    (hf : ∀ t, f t ∈ AddCircle.closedIntervalArc p a b) :
    ∃ n : C(unitInterval, ℝ), (∀ t, n t ∈ Icc a b) ∧
      (∀ t, (n t : C0) = f t) ∧ ∀ s t, f s = f t → n s = n t := by
  let A := AddCircle.openPartialHomeomorphCoe p cut
  have hsource {r : ℝ} (hr : r ∈ Icc a b) : r ∈ A.source :=
    ⟨ha.trans_le hr.1, hr.2.trans_lt hb⟩
  have htarget (t : unitInterval) : f t ∈ A.target := by
    obtain ⟨r, hr, hrt⟩ := hf t
    rw [← hrt]
    exact A.map_source (hsource hr)
  let n : C(unitInterval, ℝ) :=
    ⟨fun t => A.symm (f t), A.continuousOn_symm.comp_continuous f.continuous htarget⟩
  refine ⟨n, ?_, fun t => A.right_inv (htarget t), ?_⟩
  · intro t
    obtain ⟨r, hr, hrt⟩ := hf t
    change A.symm (f t) ∈ Icc a b
    rw [← hrt]
    change A.symm (A r) ∈ Icc a b
    rw [A.left_inv (hsource hr)]
    exact hr
  · intro s t hst
    exact congrArg A.symm hst

theorem exists_hamiltonZero_rectangular_path_contraction
    (u : C(unitInterval, X0)) (hu : u 0 = u 1)
    {cut alpha beta cut' a b : ℝ}
    (halpha : cut < alpha) (hbeta : beta < cut + p)
    (ha : cut' < a) (hb : b < cut' + p)
    (hfirst : ∀ t, (Q0 (u t)).2 ∈ AddCircle.closedIntervalArc p alpha beta)
    (hsecond : ∀ t, (Q0 (u t)).1.2 ∈ AddCircle.closedIntervalArc p a b)
    (theta : C0) (hthird : ∀ t, (Q0 (u t)).1.1 = theta) :
    ∃ F : u.HomotopyRel (ContinuousMap.const unitInterval (u 0)) ({0, 1} : Set unitInterval),
      ∀ s t, (Q0 (F (s, t))).1.1 = theta ∧
        (Q0 (F (s, t))).2 ∈ AddCircle.closedIntervalArc p alpha beta ∧
        (Q0 (F (s, t))).1.2 ∈ AddCircle.closedIntervalArc p a b := by
  let f : C(unitInterval, C0) := ⟨fun t => (Q0 (u t)).2, by fun_prop⟩
  let g : C(unitInterval, C0) := ⟨fun t => (Q0 (u t)).1.2, by fun_prop⟩
  obtain ⟨n, hn, hnf, hnunique⟩ := continuous_short_arc_lift f halpha hbeta hfirst
  obtain ⟨m, hm, hmg, hmunique⟩ := continuous_short_arc_lift g ha hb hsecond
  have hnends : n 0 = n 1 := hnunique 0 1 (congrArg (fun x => (Q0 x).2) hu)
  have hmends : m 0 = m 1 := hmunique 0 1 (congrArg (fun x => (Q0 x).1.2) hu)
  let mix (v : C(unitInterval, ℝ)) (s t : unitInterval) : ℝ :=
    (1 - (s : ℝ)) * v t + (s : ℝ) * v 0
  let G : C(unitInterval × unitInterval, X0) :=
    ⟨fun st => (Q0).symm ((theta, ((mix m st.1 st.2 : ℝ) : C0)),
      ((mix n st.1 st.2 : ℝ) : C0)), by dsimp [mix]; fun_prop⟩
  have hG (s t : unitInterval) : Q0 (G (s, t)) =
      ((theta, ((mix m s t : ℝ) : C0)), ((mix n s t : ℝ) : C0)) :=
    (Q0).apply_symm_apply _
  have hcoord (t : unitInterval) :
      ((theta, (m t : C0)), (n t : C0)) = Q0 (u t) := by
    rw [hnf, hmg]
    exact Prod.ext (Prod.ext (hthird t).symm rfl) rfl
  have hzero (t : unitInterval) : G (0, t) = u t := by
    apply (Q0).injective
    rw [hG]
    simpa only [mix, Set.Icc.coe_zero, sub_zero, one_mul, zero_mul, add_zero] using hcoord t
  have hone (t : unitInterval) : G (1, t) = u 0 := by
    apply (Q0).injective
    rw [hG]
    simpa only [mix, Set.Icc.coe_one, sub_self, zero_mul, one_mul, zero_add] using hcoord 0
  have hfixed (s t : unitInterval) (ht : t = 0 ∨ t = 1) : G (s, t) = u t := by
    apply (Q0).injective
    rw [hG]
    have hnkeep : mix n s t = n t := by
      rcases ht with rfl | rfl
      · dsimp [mix]; ring
      · dsimp [mix]; rw [hnends]; ring
    have hmkeep : mix m s t = m t := by
      rcases ht with rfl | rfl
      · dsimp [mix]; ring
      · dsimp [mix]; rw [hmends]; ring
    rw [hnkeep, hmkeep]
    exact hcoord t
  let F : u.HomotopyRel (ContinuousMap.const unitInterval (u 0))
      ({0, 1} : Set unitInterval) := {
    toFun := G
    continuous_toFun := G.continuous
    map_zero_left := hzero
    map_one_left := hone
    prop' := by
      intro s t ht
      exact hfixed s t (by simpa only [mem_insert_iff, mem_singleton_iff] using ht) }
  refine ⟨F, ?_⟩
  intro s t
  change (Q0 (G (s, t))).1.1 = theta ∧
    (Q0 (G (s, t))).2 ∈ AddCircle.closedIntervalArc p alpha beta ∧
    (Q0 (G (s, t))).1.2 ∈ AddCircle.closedIntervalArc p a b
  rw [hG]
  refine ⟨rfl, ⟨mix n s t, ?_, rfl⟩, ⟨mix m s t, ?_, rfl⟩⟩
  · exact (convex_Icc alpha beta) (hn t) (hn 0)
      (by linarith [s.property.2]) s.property.1 (by ring)
  · exact (convex_Icc a b) (hm t) (hm 0)
      (by linarith [s.property.2]) s.property.1 (by ring)

theorem exists_hamiltonZero_source_disk_failure_arc
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    (phi : C(H0, H0)) {R S : Set X0} (hRclosed : IsClosed R) (hS : S ⊆ R)
    (H : D ≃ₜ S) (j : V2 → X0) (hj : PolyhedralPLInCharts e j D)
    (hJ : ∀ z : D, j z = (H z : X0))
    (hproper : ∀ z : D, (H z : X0) ∈ frontier R ↔ (z : V2) ∈ Q)
    {cut alpha beta cut' a b : ℝ}
    (halpha : cut < alpha) (hbeta : beta < cut + p)
    (ha : cut' < a) (hb : b < cut' + p)
    (hfirst : ∀ z ∈ D, hamiltonZeroCircleMap phi (j z) ∈
      AddCircle.closedIntervalArc p alpha beta)
    (hsecond : ∀ z ∈ D, hamiltonZeroSecondCircleMap phi (j z) ∈
      AddCircle.closedIntervalArc p a b)
    (theta : C0) (hthird : ∀ z ∈ D, hamiltonZeroThirdCircleMap phi (j z) = theta)
    (x y : V2) (hx : x ∈ Q) (hy : y ∈ Q) (hne : x ≠ y)
    (heq : hamiltonZeroAmbientMap phi (j x) = hamiltonZeroAmbientMap phi (j y)) :
    ∃ (param : ℝ → V2) (k : C(unitInterval, X0)),
      FinitePiecewiseAffineOn param (Icc (0 : ℝ) 1) ∧
      PolyhedralPLInCharts e (j ∘ param) (Icc (0 : ℝ) 1) ∧
      (∀ t : unitInterval, param t ∈ D ∧ j (param t) = k t) ∧
      Topology.IsEmbedding k ∧ k 0 = j x ∧ k 1 = j y ∧ k 0 ≠ k 1 ∧
      range k ⊆ S ∧ (∀ t, k t ∈ frontier R ↔ t = 0 ∨ t = 1) ∧
      (∀ t, k t ∈ interior R ↔ t ≠ 0 ∧ t ≠ 1) ∧
      ∃ F : ((hamiltonZeroAmbientMap phi).comp k).HomotopyRel
          (ContinuousMap.const unitInterval (hamiltonZeroAmbientMap phi (j x)))
          ({0, 1} : Set unitInterval),
        ∀ s t, (Q0 (F (s, t))).1.1 = theta ∧
          (Q0 (F (s, t))).2 ∈ AddCircle.closedIntervalArc p alpha beta ∧
          (Q0 (F (s, t))).1.2 ∈ AddCircle.closedIntervalArc p a b := by
  obtain ⟨param, arc, hparamPL, hparam, harc, hzero, hone, hD, hrim⟩ :=
    exists_unit_square_proper_PL_arc x y hx hy hne
  let arcD : C(unitInterval, D) :=
    ⟨fun t => ⟨arc t, hD (mem_range_self t)⟩, arc.continuous.subtype_mk _⟩
  let k : C(unitInterval, X0) := ⟨fun t => (H (arcD t) : X0), by fun_prop⟩
  have hparamD (t : unitInterval) : param t ∈ D := by
    rw [hparam]
    exact hD (mem_range_self t)
  have hkv (t : unitInterval) : j (param t) = k t := by
    rw [hparam]
    exact hJ (arcD t)
  have hk0 : k 0 = j x := by
    rw [← hkv, hparam, hzero]
  have hk1 : k 1 = j y := by
    rw [← hkv, hparam, hone]
  have hjparam : PolyhedralPLInCharts e (j ∘ param) (Icc (0 : ℝ) 1) := by
    have hparamPL' := hparamPL
    obtain ⟨K, hK, hKI, _⟩ := hparamPL
    have hmap : MapsTo param K.space D := by
      intro t ht
      exact hparamD ⟨t, hKI.subset ht⟩
    have hh := hj.comp_finitePiecewiseAffineOn K hK
      (hKI.symm ▸ hparamPL') hmap
    simpa only [hKI] using hh
  have hkemb : Topology.IsEmbedding k := by
    have hDemb : Topology.IsEmbedding arcD :=
      arcD.continuous.isClosedEmbedding
        (fun _ _ hst => harc.injective (congrArg Subtype.val hst)) |>.isEmbedding
    exact (Topology.IsEmbedding.subtypeVal.comp H.isEmbedding).comp hDemb
  have hkS : range k ⊆ S := by
    rintro _ ⟨t, rfl⟩
    exact (H (arcD t)).property
  have hkfront (t : unitInterval) : k t ∈ frontier R ↔ t = 0 ∨ t = 1 :=
    (hproper (arcD t)).trans (hrim t)
  have hkint (t : unitInterval) : k t ∈ interior R ↔ t ≠ 0 ∧ t ≠ 1 := by
    have hmem := hS (hkS (mem_range_self t))
    have hf : k t ∈ frontier R ↔ k t ∉ interior R := by
      rw [hRclosed.frontier_eq]
      exact and_iff_right hmem
    rw [← not_or, ← hkfront, hf, not_not]
  let u := (hamiltonZeroAmbientMap phi).comp k
  have hu : u 0 = u 1 := by
    change hamiltonZeroAmbientMap phi (k 0) = hamiltonZeroAmbientMap phi (k 1)
    rw [hk0, hk1]
    exact heq
  have hufirst (t : unitInterval) : (Q0 (u t)).2 ∈
      AddCircle.closedIntervalArc p alpha beta := by
    change (Q0 (hamiltonZeroAmbientMap phi (k t))).2 ∈ _
    rw [← hkv]
    exact hfirst (param t) (hparamD t)
  have husecond (t : unitInterval) : (Q0 (u t)).1.2 ∈
      AddCircle.closedIntervalArc p a b := by
    change (Q0 (hamiltonZeroAmbientMap phi (k t))).1.2 ∈ _
    rw [← hkv, ← hamiltonZeroSecondCircleMap_ambient]
    exact hsecond (param t) (hparamD t)
  have huthird (t : unitInterval) : (Q0 (u t)).1.1 = theta := by
    change (Q0 (hamiltonZeroAmbientMap phi (k t))).1.1 = _
    rw [← hkv, ← hamiltonZeroThirdCircleMap_ambient]
    exact hthird (param t) (hparamD t)
  obtain ⟨F, hF⟩ := exists_hamiltonZero_rectangular_path_contraction u hu
    halpha hbeta ha hb hufirst husecond theta huthird
  have hconst : ContinuousMap.const unitInterval (u 0) =
      ContinuousMap.const unitInterval (hamiltonZeroAmbientMap phi (j x)) := by
    congr 1
    exact congrArg (hamiltonZeroAmbientMap phi) hk0
  refine ⟨param, k, hparamPL, hjparam, fun t => ⟨hparamD t, hkv t⟩, hkemb,
    hk0, hk1, fun hh => zero_ne_one (hkemb.injective hh), hkS, hkfront, hkint,
    F.cast rfl hconst, ?_⟩
  exact hF

end PoincareConjecture.M76
