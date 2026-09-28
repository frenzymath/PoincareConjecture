import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Maps.DiskBoundaryFailure
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Coverings.PointedFiberTails
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Spheres.Elimination
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Paths.EmbeddedConcatenation
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Paths.PLConcatenation









set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Ann" => squareAnnulus 8 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

private instance : Fact (0 < p) := ⟨by norm_num⟩

private theorem unfolded_interval_coordinate
    {cut alpha beta delta0 delta1 : ℝ}
    (halpha : cut < alpha) (hab : alpha < beta) (hbeta : beta < cut + p)
    (hd0 : delta0 ∈ ({alpha, beta} : Set ℝ))
    (hd1 : delta1 ∈ ({alpha, beta} : Set ℝ)) (hne : delta0 ≠ delta1) :
    (∀ t : unitInterval, (delta1 - delta0) * (t : ℝ) + delta0 ∈ Icc alpha beta) ∧
    Function.Injective (fun t : unitInterval =>
      (((delta1 - delta0) * (t : ℝ) + delta0 : ℝ) : C0)) ∧
    (∀ t : unitInterval,
      (((delta1 - delta0) * (t : ℝ) + delta0 : ℝ) : C0) ∈
        ({(alpha : C0), (beta : C0)} : Set C0) ↔ t = 0 ∨ t = 1) ∧
    ∃ side : Bool, (if side then delta1 else delta0) = alpha := by
  have hrange (t : unitInterval) :
      (delta1 - delta0) * (t : ℝ) + delta0 ∈ Icc alpha beta := by
    rcases hd0 with rfl | hd0 <;> rcases hd1 with rfl | hd1
    all_goals try simp only [mem_singleton_iff] at *
    all_goals subst_vars
    all_goals constructor <;> nlinarith [t.property.1, t.property.2]
  let A := AddCircle.openPartialHomeomorphCoe p cut
  have hsource {x : ℝ} (hx : x ∈ Icc alpha beta) : x ∈ A.source :=
    ⟨halpha.trans_le hx.1, hx.2.trans_lt hbeta⟩
  have hi : Function.Injective (fun t : unitInterval =>
      (((delta1 - delta0) * (t : ℝ) + delta0 : ℝ) : C0)) := by
    intro s t hst
    have h := A.injOn (hsource (hrange s)) (hsource (hrange t)) hst
    apply Subtype.ext
    exact mul_left_cancel₀ (sub_ne_zero.mpr (Ne.symm hne)) (by linarith)
  refine ⟨hrange, hi, ?_, ?_⟩
  · intro t
    have heq0 : (((delta1 - delta0) * ((0 : unitInterval) : ℝ) + delta0 : ℝ) : C0) =
        (delta0 : C0) := by simp
    have heq1 : (((delta1 - delta0) * ((1 : unitInterval) : ℝ) + delta0 : ℝ) : C0) =
        (delta1 : C0) := by simp
    have hset : ({(alpha : C0), (beta : C0)} : Set C0) =
        {(delta0 : C0), (delta1 : C0)} := by
      rcases hd0 with rfl | hd0 <;> rcases hd1 with rfl | hd1
      all_goals try simp only [mem_singleton_iff] at *
      all_goals subst_vars
      all_goals first | contradiction | rfl | exact pair_comm _ _
    rw [hset, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl (hi (h.trans heq0.symm))
      · exact Or.inr (hi (h.trans heq1.symm))
    · rintro (rfl | rfl)
      · exact Or.inl heq0
      · exact Or.inr heq1
  · rcases hd0 with hd0 | hd0
    · exact ⟨false, hd0⟩
    · have hd0' : delta0 = beta := hd0
      rcases hd1 with hd1 | hd1
      · exact ⟨true, hd1⟩
      · exact False.elim (hne (hd0'.trans hd1.symm))

private theorem interval_homeomorph_end_iff (H : unitInterval ≃ₜ unitInterval)
    (t : unitInterval) : H t = 0 ∨ H t = 1 ↔ t = 0 ∨ t = 1 := by
  constructor
  · rintro (h | h)
    · have ht : t = H.symm 0 := H.injective (by simp [h])
      rw [ht]
      exact interval_homeomorph_preimage_endpoint H false
    · have ht : t = H.symm 1 := H.injective (by simp [h])
      rw [ht]
      exact interval_homeomorph_preimage_endpoint H true
  · rintro (rfl | rfl)
    · exact interval_homeomorph_preimage_endpoint H.symm false
    · exact interval_homeomorph_preimage_endpoint H.symm true



theorem hamiltonZero_installed_unfolded_annulus_frontier_iff
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3} {R : Set X0}
    {j : ℝ × ℝ → X0} {phi : C(H0, H0)} {c : C(Ann, unitInterval × C0)}
    (harcs : HamiltonZeroInstalledAnnulusPLArcFibers e R j phi c)
    (hc : IsCoveringMap c)
    {cut alpha beta delta0 delta1 : ℝ}
    (halpha : cut < alpha) (hab : alpha < beta) (hbeta : beta < cut + p)
    (hd0 : delta0 ∈ ({alpha, beta} : Set ℝ))
    (hd1 : delta1 ∈ ({alpha, beta} : Set ℝ)) (hne : delta0 ≠ delta1)
    (theta : C0)
    (hformula : ∀ z : Ann, hamiltonZeroAmbientMap phi (j z) =
      hamiltonZeroAnnulusTargetMap delta0 delta1 theta (c z)) (z : Ann) :
    j z ∈ frontier R ↔
      hamiltonZeroCircleMap phi (j z) ∈ ({(alpha : C0), (beta : C0)} : Set C0) := by
  obtain ⟨n, arc, _, H, _, _, _, _, _, hwhole, hmark, hH, _, _⟩ :=
    harcs.exists_pointed_tail_family hc (c z).2
  obtain ⟨i, s, hs⟩ := mem_iUnion.mp (hwhole.symm.subset (show (c z).2 = (c z).2 from rfl))
  have hcoord : hamiltonZeroCircleMap phi (j z) =
      (((delta1 - delta0) * ((c z).1 : ℝ) + delta0 : ℝ) : C0) := by
    exact congrArg Prod.snd ((congrArg Q0 (hformula z)).trans
      (hamiltonZeroAnnulusTargetMap_coordinates delta0 delta1 theta (c z)))
  rw [hcoord, (unfolded_interval_coordinate halpha hab hbeta hd0 hd1 hne).2.2.1]
  rw [← hs, ← hH, interval_homeomorph_end_iff]
  exact hmark i s

private theorem reverse_original_PL_arc
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3} {f : ℝ → X0}
    (hf : PolyhedralPLInCharts e f (Icc (0 : ℝ) 1)) :
    PolyhedralPLInCharts e (fun t => f (1 - t)) (Icc (0 : ℝ) 1) := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKI, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)
  let A : ℝ →ᴬ[ℝ] ℝ := ContinuousAffineMap.const ℝ ℝ 1 - ContinuousAffineMap.id ℝ ℝ
  have hA : MapsTo A K.space (Icc (0 : ℝ) 1) := by
    intro t ht
    have ht' := hKI.subset ht
    change 0 ≤ 1 - t ∧ 1 - t ≤ 1
    constructor <;> linarith [ht'.1, ht'.2]
  have h := hf.comp_finitePiecewiseAffineOn K hK
    (show FinitePiecewiseAffineOn A K.space from ⟨K, hK, rfl, K.affineOnFaces_affine A⟩) hA
  rw [hKI] at h
  apply h.congr
  intro t _
  change f ((ContinuousAffineMap.const ℝ ℝ 1 - ContinuousAffineMap.id ℝ ℝ : ℝ →ᴬ[ℝ] ℝ) t) = f (1 - t)
  rw [ContinuousAffineMap.sub_apply]
  rfl

private theorem extend_marked_disk_path
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3} {R N : Set X0}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (k left right : C(unitInterval, X0))
    (hk : Topology.IsEmbedding k) (hleft : Topology.IsEmbedding left)
    (hright : Topology.IsEmbedding right)
    (hleft0 : left 0 = k 0) (hright0 : right 0 = k 1)
    (hkfront : ∀ t, k t ∈ frontier N ↔ t = 0 ∨ t = 1)
    (hkint : range k ⊆ interior R)
    (hleftN : range left ⊆ frontier N) (hrightN : range right ⊆ frontier N)
    (hleftfront : ∀ t, left t ∈ frontier R ↔ t = 1)
    (hrightfront : ∀ t, right t ∈ frontier R ↔ t = 1)
    (hdis : Disjoint (range left) (range right))
    (f g h : ℝ → X0)
    (hf : PolyhedralPLInCharts e f (Icc (0 : ℝ) 1))
    (hg : PolyhedralPLInCharts e g (Icc (0 : ℝ) 1))
    (hh : PolyhedralPLInCharts e h (Icc (0 : ℝ) 1))
    (hfk : ∀ t : unitInterval, f t = k t)
    (hgl : ∀ t : unitInterval, g t = left t)
    (hhr : ∀ t : unitInterval, h t = right t) :
    ∃ (P : ℝ → X0) (K : Path (left 1) (right 1)),
      PolyhedralPLInCharts e P (Icc (0 : ℝ) 1) ∧
      (∀ t : unitInterval, P t = K t) ∧ Topology.IsEmbedding K ∧
      range K = (range left ∪ range k) ∪ range right ∧
      (∀ t, K t ∈ frontier R ↔ t = 0 ∨ t = 1) := by
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let a : Path (left 1) (k 0) :=
    { toFun := fun t => left (unitInterval.symm t)
      continuous_toFun := left.continuous.comp unitInterval.continuous_symm
      source' := by simp
      target' := by simpa using hleft0 }
  let b : Path (k 0) (k 1) := { toContinuousMap := k, source' := rfl, target' := rfl }
  let c : Path (k 1) (right 1) := { toContinuousMap := right, source' := hright0, target' := rfl }
  have ha : Topology.IsEmbedding a := hleft.comp unitInterval.symmHomeomorph.isEmbedding
  have harange : range a = range left := unitInterval.symm_involutive.surjective.range_comp left
  have hnotright : k 1 ∉ range a := by
    rw [harange]
    intro hx
    exact disjoint_left.mp hdis hx ⟨0, hright0⟩
  have habrange : range a ∩ range b ⊆ {k 0} :=
    a.range_inter_subset_endpoint_of_frontier b (harange ▸ hleftN)
      (fun t ht => (hkfront t).mp ht) hnotright
  have hbcrange : range b ∩ range c ⊆ {k 1} := by
    rintro x ⟨⟨t, rfl⟩, hx⟩
    rcases (hkfront t).mp (hrightN hx) with ht | ht
    · exact False.elim (disjoint_left.mp hdis ⟨0, hleft0⟩ (ht ▸ hx))
    · simp [b, ht]
  have hac : Disjoint (range a) (range c) := by
    rw [harange]
    exact hdis
  let K := (a.trans b).trans c
  have hK : Topology.IsEmbedding K :=
    a.isEmbedding_trans_trans_of_range_inter_subset b c ha hk hright habrange hbcrange hac
  have hrange : range K = (range left ∪ range k) ∪ range right := by
    simp only [K, Path.trans_range, harange]
    rfl
  let P := intervalConcatenation (intervalConcatenation (fun t => g (1 - t)) f) h
  have hga (t : unitInterval) : g (1 - (t : ℝ)) = a t := hgl (unitInterval.symm t)
  have hgab : ∀ t : unitInterval,
      intervalConcatenation (fun t => g (1 - t)) f t = a.trans b t :=
    intervalConcatenation_eq_path_trans a b hga hfk
  have hfirstPL := (reverse_original_PL_arc hg).interval_concatenation hcompat hf (by
    simpa using (hgl 0).trans (hleft0.trans (hfk 0).symm))
  have hPL : PolyhedralPLInCharts e P (Icc (0 : ℝ) 1) :=
    hfirstPL.interval_concatenation hcompat hh (by
      exact (hgab 1).trans ((a.trans b).target.trans (hright0.symm.trans (hhr 0).symm)))
  refine ⟨P, K, hPL, intervalConcatenation_eq_path_trans (a.trans b) c hgab hhr,
    hK, hrange, ?_⟩
  intro t
  constructor
  · intro ht
    have hx : K t ∈ (range left ∪ range k) ∪ range right := hrange.subset ⟨t, rfl⟩
    rcases hx with (⟨s, hs⟩ | ⟨s, hs⟩) | ⟨s, hs⟩
    · have hs1 : s = 1 := (hleftfront s).mp (hs ▸ ht)
      exact Or.inl (hK.injective (hs.symm.trans (hs1 ▸ K.source.symm)))
    · exact False.elim (ht.2 (hs ▸ hkint ⟨s, rfl⟩))
    · have hs1 : s = 1 := (hrightfront s).mp (hs ▸ ht)
      exact Or.inr (hK.injective (hs.symm.trans (hs1 ▸ K.target.symm)))
  · rintro (rfl | rfl)
    · rw [K.source]
      exact (hleftfront 1).mpr rfl
    · rw [K.target]
      exact (hrightfront 1).mpr rfl




theorem exists_hamiltonZero_extended_disk_failure_arc
    {ι η : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    (chi psi : C(H0, H0)) {R N : Set X0}
    (heR : PLDomain e R) (hN : IsClosed N) (hNR : N ⊆ R)
    (j : η → ℝ × ℝ → X0)
    (hfront : frontier N = (N ∩ frontier R) ∪ ⋃ i, j i '' Ann)
    (hdis : Pairwise (fun i k => Disjoint (j i '' Ann) (j k '' Ann)))
    (hj : ∀ i, Topology.IsEmbedding (fun z : Ann => j i z))
    (delta0 delta1 : η → ℝ) (phase : η → C0)
    (c : η → C(Ann, unitInterval × C0)) (hc : ∀ i, IsCoveringMap (c i))
    (hformula : ∀ i (z : Ann), hamiltonZeroAmbientMap chi (j i z) =
      hamiltonZeroAnnulusTargetMap (delta0 i) (delta1 i) (phase i) (c i z))
    (harcs : ∀ i, HamiltonZeroInstalledAnnulusPLArcFibers e R (j i) chi (c i))
    (hfixed : EqOn (hamiltonZeroAmbientMap psi) (hamiltonZeroAmbientMap chi) (frontier N))
    {cut alpha beta cut' a b : ℝ}
    (halpha : cut < alpha) (hab : alpha < beta) (hbeta : beta < cut + p)
    (ha : cut' < a) (hb : b < cut' + p)
    (hd0 : ∀ i, delta0 i ∈ ({alpha, beta} : Set ℝ))
    (hd1 : ∀ i, delta1 i ∈ ({alpha, beta} : Set ℝ))
    (hnofold : ∀ i, delta0 i ≠ delta1 i)
    (hRfront : frontier R ⊆ hamiltonZeroCircleMap chi ⁻¹' {(alpha : C0), (beta : C0)})
    (disk : V2 → X0) (theta : C0)
    (failure : HamiltonZeroDiskFailureArc e N psi disk theta alpha beta a b) :
    ∃ (P : ℝ → X0) (K : C(unitInterval, X0)),
      PolyhedralPLInCharts e P (Icc (0 : ℝ) 1) ∧
      (∀ t : unitInterval, P t = K t) ∧ Topology.IsEmbedding K ∧
      range K ⊆ R ∧ (∀ t, K t ∈ frontier R ↔ t = 0 ∨ t = 1) ∧
      (∀ t, K t ∈ interior R ↔ t ≠ 0 ∧ t ≠ 1) ∧
      ∃ F : ((hamiltonZeroAmbientMap psi).comp K).HomotopyRel
          (ContinuousMap.const unitInterval (hamiltonZeroAmbientMap psi (K 0)))
          ({0, 1} : Set unitInterval),
        ∀ s t, (Q0 (F (s, t))).1.1 = theta ∧
          (Q0 (F (s, t))).2 ∈ AddCircle.closedIntervalArc p alpha beta ∧
          (Q0 (F (s, t))).1.2 ∈ AddCircle.closedIntervalArc p a b := by
  classical
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  obtain ⟨param, k, _, hparamPL, hparam, hk, hkne, _, hkfront, hkint, F, hF⟩ := failure
  have hkN (t : unitInterval) : k t ∈ N := by
    by_cases ht : t = 0 ∨ t = 1
    · exact hN.frontier_subset ((hkfront t).mpr ht)
    · exact interior_subset ((hkint t).mpr (by tauto))
  have hkR : range k ⊆ R := by rintro _ ⟨t, rfl⟩; exact hNR (hkN t)
  have hcoords (t : unitInterval) :
      hamiltonZeroThirdCircleMap psi (k t) = theta ∧
      hamiltonZeroCircleMap psi (k t) ∈ AddCircle.closedIntervalArc p alpha beta ∧
      hamiltonZeroSecondCircleMap psi (k t) ∈ AddCircle.closedIntervalArc p a b := by
    change (Q0 (hamiltonZeroAmbientMap psi (k t))).1.1 = theta ∧
      (Q0 (hamiltonZeroAmbientMap psi (k t))).2 ∈ _ ∧
      (Q0 (hamiltonZeroAmbientMap psi (k t))).1.2 ∈ _
    simpa only [F.apply_zero, ContinuousMap.comp_apply] using hF 0 t
  have hsame : hamiltonZeroAmbientMap psi (k 0) = hamiltonZeroAmbientMap psi (k 1) :=
    (F.fst_eq_snd (by simp : (1 : unitInterval) ∈ ({0, 1} : Set unitInterval))).symm
  have hfamfront (i : η) : j i '' Ann ⊆ frontier N := by
    rw [hfront]
    exact fun x hx => Or.inr (mem_iUnion.mpr ⟨i, hx⟩)
  have hformulaPsi (i : η) (z : Ann) : hamiltonZeroAmbientMap psi (j i z) =
      hamiltonZeroAnnulusTargetMap (delta0 i) (delta1 i) (phase i) (c i z) :=
    (hfixed (hfamfront i ⟨z, z.property, rfl⟩)).trans (hformula i z)
  have hboundary (x : X0) (hx : x ∈ frontier N) : x ∈ frontier R ↔
      hamiltonZeroCircleMap psi x ∈ ({(alpha : C0), (beta : C0)} : Set C0) := by
    have heq : hamiltonZeroCircleMap psi x = hamiltonZeroCircleMap chi x :=
      congrArg (fun y => (Q0 y).2) (hfixed hx)
    rw [heq]
    constructor
    · exact fun ht => hRfront ht
    · intro ht
      rw [hfront] at hx
      rcases hx with hx | hx
      · exact hx.2
      · obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hx
        exact (hamiltonZero_installed_unfolded_annulus_frontier_iff (harcs i) (hc i)
          halpha hab hbeta (hd0 i) (hd1 i) (hnofold i) (phase i) (hformula i) ⟨z, hz⟩).mpr ht
  have hboth : k 0 ∈ frontier R ↔ k 1 ∈ frontier R := by
    rw [hboundary _ ((hkfront 0).mpr (Or.inl rfl)),
      hboundary _ ((hkfront 1).mpr (Or.inr rfl))]
    exact Iff.of_eq (congrArg (fun y => (Q0 y).2 ∈
      ({(alpha : C0), (beta : C0)} : Set C0)) hsame)
  have hinterior (K : C(unitInterval, X0)) (hKR : range K ⊆ R)
      (hproper : ∀ t, K t ∈ frontier R ↔ t = 0 ∨ t = 1) :
      ∀ t, K t ∈ interior R ↔ t ≠ 0 ∧ t ≠ 1 := by
    intro t
    have hm := hKR ⟨t, rfl⟩
    have hf : K t ∈ frontier R ↔ K t ∉ interior R := by
      rw [heR.closed.frontier_eq]
      exact and_iff_right hm
    rw [← not_or, ← hproper, hf, not_not]
  by_cases hstart : k 0 ∈ frontier R
  · have hend := hboth.mp hstart
    have hproper (t : unitInterval) : k t ∈ frontier R ↔ t = 0 ∨ t = 1 := by
      constructor
      · intro ht
        by_contra hends
        exact ht.2 (interior_mono hNR ((hkint t).mpr (by tauto)))
      · rintro (rfl | rfl)
        · exact hstart
        · exact hend
    exact ⟨disk ∘ param, k, hparamPL, fun t => (hparam t).2, hk, hkR, hproper,
      hinterior k hkR hproper, F, hF⟩
  have hend : k 1 ∉ frontier R := fun h => hstart (hboth.mpr h)
  have hkRint : range k ⊆ interior R := by
    rintro _ ⟨t, rfl⟩
    by_cases ht : t = 0 ∨ t = 1
    · have hnot : k t ∉ frontier R := by rcases ht with rfl | rfl; exact hstart; exact hend
      have hm := hkR ⟨t, rfl⟩
      rw [heR.closed.frontier_eq] at hnot
      exact not_not.mp (fun hi => hnot ⟨hm, hi⟩)
    · exact interior_mono hNR ((hkint t).mpr (by tauto))
  have hselect (t : unitInterval) (ht : t = 0 ∨ t = 1) (hnt : k t ∉ frontier R) :
      ∃ (i : η) (z : Ann), j i z = k t := by
    have hx := (hkfront t).mpr ht
    rw [hfront] at hx
    rcases hx with hx | hx
    · exact False.elim (hnt hx.2)
    · obtain ⟨i, z, hz, hzk⟩ := mem_iUnion.mp hx
      exact ⟨i, ⟨z, hz⟩, hzk⟩
  obtain ⟨i0, z0, hz0⟩ := hselect 0 (Or.inl rfl) hstart
  obtain ⟨i1, z1, hz1⟩ := hselect 1 (Or.inr rfl) hend
  have hn0 : j i0 z0 ∉ frontier R := hz0 ▸ hstart
  have hn1 : j i1 z1 ∉ frontier R := hz1 ▸ hend
  choose side hside using fun i =>
    (unfolded_interval_coordinate halpha hab hbeta (hd0 i) (hd1 i) (hnofold i)).2.2.2
  have htailpair :
      ∃ (l r : C(unitInterval, Ann)) (ql qr : ℝ → ℝ × ℝ),
        HamiltonZeroPointedInteriorFiberTail e R (j i0) (c i0) z0 (side i0) l ql ∧
        HamiltonZeroPointedInteriorFiberTail e R (j i1) (c i1) z1 (side i1) r qr ∧
        Disjoint (range (fun t => j i0 (l t))) (range (fun t => j i1 (r t))) := by
    by_cases hi : i0 = i1
    · subst i1
      have heq : c i0 z0 = c i0 z1 := by
        have hh := congrArg Q0 (hz0 ▸ hz1 ▸ hsame)
        rw [hformulaPsi, hformulaPsi, hamiltonZeroAnnulusTargetMap_coordinates,
          hamiltonZeroAnnulusTargetMap_coordinates] at hh
        exact Prod.ext
          ((unfolded_interval_coordinate halpha hab hbeta (hd0 i0) (hd1 i0) (hnofold i0)).2.1
            (congrArg Prod.snd hh))
          (congrArg (fun y : (C0 × C0) × C0 => y.1.1) hh)
      let z : Bool → Ann := fun s => if s then z1 else z0
      obtain ⟨tail, q, ht, hd⟩ := (harcs i0).exists_pointed_interior_tails (hc i0) z
        (by intro s; cases s; exact hn0; exact hn1)
        heq (fun _ => side i0)
      have hzne : z false ≠ z true := by
        intro h
        exact hkne (hz0.symm.trans ((congrArg (fun w : Ann => j i0 w) h).trans hz1))
      refine ⟨tail false, tail true, q false, q true, ht false, ht true, ?_⟩
      apply disjoint_left.mpr
      rintro _ ⟨s, hs⟩ ⟨t, ht'⟩
      have hst := (hj i0).injective (hs.trans ht'.symm)
      exact disjoint_left.mp (hd hzne) ⟨s, rfl⟩ ⟨t, hst.symm⟩
    · obtain ⟨l, ql, hl⟩ := (harcs i0).exists_pointed_interior_tail (hc i0) z0 hn0 (side i0)
      obtain ⟨r, qr, hr⟩ := (harcs i1).exists_pointed_interior_tail (hc i1) z1 hn1 (side i1)
      refine ⟨l, r, ql, qr, hl, hr, (hdis hi).mono ?_ ?_⟩
      · rintro _ ⟨t, rfl⟩
        exact ⟨l t, (l t).property, rfl⟩
      · rintro _ ⟨t, rfl⟩
        exact ⟨r t, (r t).property, rfl⟩
  obtain ⟨l, r, ql, qr, hl, hr, htaildis⟩ := htailpair
  let left : C(unitInterval, X0) := ⟨fun t => j i0 (l t), (hj i0).continuous.comp l.continuous⟩
  let right : C(unitInterval, X0) := ⟨fun t => j i1 (r t), (hj i1).continuous.comp r.continuous⟩
  have hleft0 : left 0 = k 0 := (congrArg (fun z : Ann => j i0 z) hl.start).trans hz0
  have hright0 : right 0 = k 1 := (congrArg (fun z : Ann => j i1 z) hr.start).trans hz1
  have hleftN : range left ⊆ frontier N := by
    rintro _ ⟨t, rfl⟩
    exact hfamfront i0 ⟨l t, (l t).property, rfl⟩
  have hrightN : range right ⊆ frontier N := by
    rintro _ ⟨t, rfl⟩
    exact hfamfront i1 ⟨r t, (r t).property, rfl⟩
  obtain ⟨P, K, hP, hPK, hK, hKrange, hKproper⟩ :=
    extend_marked_disk_path heR.compatible k left right hk
      ((hj i0).comp hl.embedding) ((hj i1).comp hr.embedding)
      hleft0 hright0 hkfront hkRint hleftN hrightN hl.proper hr.proper htaildis
      (disk ∘ param) (j i0 ∘ ql) (j i1 ∘ qr) hparamPL hl.originalPL hr.originalPL
      (fun t => (hparam t).2) (fun t => congrArg (j i0) (hl.parameter t))
      (fun t => congrArg (j i1) (hr.parameter t))
  have hKR : range K ⊆ R := by
    rw [hKrange]
    exact union_subset (union_subset (hleftN.trans (hN.frontier_subset.trans hNR)) hkR)
      (hrightN.trans (hN.frontier_subset.trans hNR))
  have htailcoords {i : η} {z : Ann} {tail : C(unitInterval, Ann)} {q : ℝ → ℝ × ℝ}
      (ht : HamiltonZeroPointedInteriorFiberTail e R (j i) (c i) z (side i) tail q)
      {s : unitInterval} (hz : j i z = k s) (t : unitInterval) :
      hamiltonZeroThirdCircleMap psi (j i (tail t)) = theta ∧
      hamiltonZeroCircleMap psi (j i (tail t)) ∈ AddCircle.closedIntervalArc p alpha beta ∧
      hamiltonZeroSecondCircleMap psi (j i (tail t)) ∈ AddCircle.closedIntervalArc p a b := by
    have htcoord := (congrArg Q0 (hformulaPsi i (tail t))).trans
      (hamiltonZeroAnnulusTargetMap_coordinates (delta0 i) (delta1 i) (phase i) (c i (tail t)))
    have hzcoord := (congrArg Q0 (hformulaPsi i z)).trans
      (hamiltonZeroAnnulusTargetMap_coordinates (delta0 i) (delta1 i) (phase i) (c i z))
    have hzthird : (c i z).2 = theta :=
      (congrArg (fun y : (C0 × C0) × C0 => y.1.1) hzcoord).symm.trans (hz ▸ (hcoords s).1)
    have hzsecond : phase i ∈ AddCircle.closedIntervalArc p a b := by
      have h : hamiltonZeroSecondCircleMap psi (j i z) = phase i :=
        congrArg (fun y : (C0 × C0) × C0 => y.1.2) hzcoord
      rw [← h, hz]
      exact (hcoords s).2.2
    change (Q0 (hamiltonZeroAmbientMap psi (j i (tail t)))).1.1 = theta ∧
      (Q0 (hamiltonZeroAmbientMap psi (j i (tail t)))).2 ∈ _ ∧
      (Q0 (hamiltonZeroAmbientMap psi (j i (tail t)))).1.2 ∈ _
    rw [htcoord, ht.phase]
    exact ⟨hzthird, ⟨_, (unfolded_interval_coordinate halpha hab hbeta
      (hd0 i) (hd1 i) (hnofold i)).1 _, rfl⟩, hzsecond⟩
  have hKcoords (t : unitInterval) :
      hamiltonZeroThirdCircleMap psi (K t) = theta ∧
      hamiltonZeroCircleMap psi (K t) ∈ AddCircle.closedIntervalArc p alpha beta ∧
      hamiltonZeroSecondCircleMap psi (K t) ∈ AddCircle.closedIntervalArc p a b := by
    have hm := hKrange.subset (mem_range_self t)
    rcases hm with (⟨s, hs⟩ | ⟨s, hs⟩) | ⟨s, hs⟩
    · exact hs ▸ htailcoords hl hz0 s
    · exact hs ▸ hcoords s
    · exact hs ▸ htailcoords hr hz1 s
  have hendpoint {i : η} {z : Ann} {tail : C(unitInterval, Ann)} {q : ℝ → ℝ × ℝ}
      (ht : HamiltonZeroPointedInteriorFiberTail e R (j i) (c i) z (side i) tail q) :
      Q0 (hamiltonZeroAmbientMap psi (j i (tail 1))) =
        (((c i z).2, phase i), (alpha : C0)) := by
    rw [hformulaPsi, hamiltonZeroAnnulusTargetMap_coordinates, ht.endpoint]
    have hh := hside i
    cases hs : side i <;> simp only [hs, Bool.false_eq_true, if_false, if_true] at hh ⊢
    all_goals simp [hh]
  have hends : hamiltonZeroAmbientMap psi (K 0) = hamiltonZeroAmbientMap psi (K 1) := by
    apply (Q0).injective
    rw [K.source, K.target]
    change Q0 (hamiltonZeroAmbientMap psi (j i0 (l 1))) =
      Q0 (hamiltonZeroAmbientMap psi (j i1 (r 1)))
    rw [hendpoint hl, hendpoint hr]
    refine Prod.ext ?_ rfl
    have heq := congrArg (fun x => (Q0 x).1) hsame
    rw [← hz0, ← hz1, hformulaPsi, hformulaPsi,
      hamiltonZeroAnnulusTargetMap_coordinates, hamiltonZeroAnnulusTargetMap_coordinates] at heq
    exact heq
  obtain ⟨G, hG⟩ := exists_hamiltonZero_rectangular_path_contraction
    ((hamiltonZeroAmbientMap psi).comp K.toContinuousMap) hends halpha hbeta ha hb
    (fun t => (hKcoords t).2.1) (fun t => (hKcoords t).2.2) theta (fun t => (hKcoords t).1)
  exact ⟨P, K.toContinuousMap, hP, hPK, hK, hKR, hKproper,
    hinterior K.toContinuousMap hKR hKproper, G, hG⟩



theorem exists_hamiltonZero_extended_second_slab_disk_failure_arc
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    (chi psi : C(H0, H0)) {R : Set X0} (heR : PLDomain e R)
    {a0 b0 : ℝ} (geometry : HamiltonZeroSecondPhaseGeometry e R chi a0 b0)
    (side : Bool) (n : Bool → ℕ)
    (j : (Σ s : Bool, Fin (n s)) → ℝ × ℝ → X0)
    (hfamily : ∀ s : Bool, (⋃ i : Fin (n s), j ⟨s, i⟩ '' Ann) =
      R ∩ hamiltonZeroSecondCircleMap chi ⁻¹' {((if s then b0 else a0 : ℝ) : C0)})
    (hdis : Pairwise (fun i k => Disjoint (j i '' Ann) (j k '' Ann)))
    (hj : ∀ i, Topology.IsEmbedding (fun z : Ann => j i z))
    (delta0 delta1 : (Σ s : Bool, Fin (n s)) → ℝ)
    (c : (Σ s : Bool, Fin (n s)) → C(Ann, unitInterval × C0))
    (hc : ∀ i, IsCoveringMap (c i))
    (hformula : ∀ i (z : Ann), hamiltonZeroAmbientMap chi (j i z) =
      hamiltonZeroAnnulusTargetMap (delta0 i) (delta1 i)
        ((if i.1 then b0 else a0 : ℝ) : C0) (c i z))
    (harcs : ∀ i, HamiltonZeroInstalledAnnulusPLArcFibers e R (j i) chi (c i))
    (G : (hamiltonZeroAmbientMap chi).HomotopyRel (hamiltonZeroAmbientMap psi)
      (interior (R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
        AddCircle.closedIntervalArc p (if side then b0 else a0) (if side then a0 + p else b0)))ᶜ)
    {cut alpha beta cut' a b : ℝ}
    (halpha : cut < alpha) (hab : alpha < beta) (hbeta : beta < cut + p)
    (ha : cut' < a) (hb : b < cut' + p)
    (hd0 : ∀ i, delta0 i ∈ ({alpha, beta} : Set ℝ))
    (hd1 : ∀ i, delta1 i ∈ ({alpha, beta} : Set ℝ))
    (hnofold : ∀ i, delta0 i ≠ delta1 i)
    (hRfront : frontier R ⊆ hamiltonZeroCircleMap chi ⁻¹' {(alpha : C0), (beta : C0)})
    (disk : V2 → X0) (theta : C0)
    (failure : HamiltonZeroDiskFailureArc e
      (R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
        AddCircle.closedIntervalArc p (if side then b0 else a0) (if side then a0 + p else b0))
      psi disk theta alpha beta a b) :
    ∃ (P : ℝ → X0) (K : C(unitInterval, X0)),
      PolyhedralPLInCharts e P (Icc (0 : ℝ) 1) ∧
      (∀ t : unitInterval, P t = K t) ∧ Topology.IsEmbedding K ∧
      range K ⊆ R ∧ (∀ t, K t ∈ frontier R ↔ t = 0 ∨ t = 1) ∧
      (∀ t, K t ∈ interior R ↔ t ≠ 0 ∧ t ≠ 1) ∧
      ∃ F : ((hamiltonZeroAmbientMap psi).comp K).HomotopyRel
          (ContinuousMap.const unitInterval (hamiltonZeroAmbientMap psi (K 0)))
          ({0, 1} : Set unitInterval),
        ∀ s t, (Q0 (F (s, t))).1.1 = theta ∧
          (Q0 (F (s, t))).2 ∈ AddCircle.closedIntervalArc p alpha beta ∧
          (Q0 (F (s, t))).1.2 ∈ AddCircle.closedIntervalArc p a b := by
  have hwhole : (⋃ i : Σ s : Bool, Fin (n s), j i '' Ann) =
      (R ∩ hamiltonZeroSecondCircleMap chi ⁻¹' {(a0 : C0)}) ∪
        (R ∩ hamiltonZeroSecondCircleMap chi ⁻¹' {(b0 : C0)}) := by
    ext x
    constructor
    · intro hx
      obtain ⟨⟨s, i⟩, hi⟩ := mem_iUnion.mp hx
      have hs := (hfamily s).subset (mem_iUnion.mpr ⟨i, hi⟩)
      cases s
      · exact Or.inl hs
      · exact Or.inr hs
    · rintro (hx | hx)
      · obtain ⟨i, hi⟩ := mem_iUnion.mp ((hfamily false).symm.subset hx)
        exact mem_iUnion.mpr ⟨⟨false, i⟩, hi⟩
      · obtain ⟨i, hi⟩ := mem_iUnion.mp ((hfamily true).symm.subset hx)
        exact mem_iUnion.mpr ⟨⟨true, i⟩, hi⟩
  exact exists_hamiltonZero_extended_disk_failure_arc chi psi heR
    (geometry.slabs side).1.closed inter_subset_left j
    (by rw [hwhole]; exact (geometry.slabs side).2.1)
    hdis hj delta0 delta1 (fun i => ((if i.1 then b0 else a0 : ℝ) : C0)) c hc hformula harcs
    (fun _ hx => (G.fst_eq_snd hx.2).symm) halpha hab hbeta ha hb hd0 hd1 hnofold hRfront
    disk theta failure

end PoincareConjecture.M76
