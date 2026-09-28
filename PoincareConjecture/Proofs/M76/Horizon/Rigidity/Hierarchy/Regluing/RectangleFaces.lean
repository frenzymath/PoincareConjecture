import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Coverings.ThirdPhaseArcs
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Coverings.MarkedCoveringPL
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.ThirdCoordinateLifts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Coverings.PointedFiberTails

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace IsCoveringMap

theorem exists_finite_lifted_compact_family
    {X Y A : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A]
    [T2Space X] [CompactSpace X] [T2Space Y] [CompactSpace A]
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    {c : C(X, Y)} (hc : IsCoveringMap c) (base : C(A, Y))
    (hbase : Function.Injective base) (a0 : A) :
    ∃ (n : ℕ) (face : Fin n → C(A, X)),
      (∀ i, Topology.IsEmbedding (face i)) ∧
      Pairwise (fun i k => Disjoint (range (face i)) (range (face k))) ∧
      (⋃ i, range (face i)) = c ⁻¹' range base ∧
      ∀ i t, c (face i t) = base t := by
  classical
  let B : Set X := c ⁻¹' {base a0}
  have hB : IsCompact B := (isClosed_singleton.preimage c.continuous).isCompact
  let : CompactSpace B := isCompact_iff_compactSpace.mp hB
  let : DiscreteTopology B := (hc (base a0)).discreteTopology_fiber
  let : Finite B := finite_of_compact_of_discrete
  let : Fintype B := Fintype.ofFinite B
  have hex (x : B) := hc.existsUnique_continuousMap_lifts base a0 x x.property
  choose lift hlift hunique using hex
  have hcoord (x : B) (t : A) : c (lift x t) = base t := congr_fun (hlift x).2 t
  have hi (x : B) : Topology.IsEmbedding (lift x) := by
    apply (lift x).continuous.isClosedEmbedding ?_ |>.isEmbedding
    intro s t hst
    apply hbase
    exact (hcoord x s).symm.trans ((congrArg c hst).trans (hcoord x t))
  have hdis : Pairwise (fun x y : B => Disjoint (range (lift x)) (range (lift y))) := by
    intro x y hxy
    apply disjoint_left.mpr
    rintro z ⟨s, rfl⟩ ⟨t, hts⟩
    have hts' : t = s := hbase ((hcoord y t).symm.trans
      ((congrArg c hts).trans (hcoord x s)))
    subst t
    have heq := hc.eq_of_comp_eq (lift y).continuous (lift x).continuous
      ((hlift y).2.trans (hlift x).2.symm) s hts
    apply hxy
    apply Subtype.ext
    exact ((hlift x).1).symm.trans ((congr_fun heq a0).symm.trans (hlift y).1)
  have hwhole : (⋃ x : B, range (lift x)) = c ⁻¹' range base := by
    ext x
    constructor
    · intro hx
      obtain ⟨z, t, rfl⟩ := mem_iUnion.mp hx
      exact ⟨t, (hcoord z t).symm⟩
    · rintro ⟨t, ht⟩
      obtain ⟨L, hL, _⟩ := hc.existsUnique_continuousMap_lifts base t x ht.symm
      have hzero : L a0 ∈ B := congr_fun hL.2 a0
      let z : B := ⟨L a0, hzero⟩
      have heq : L = lift z := hunique z L ⟨rfl, hL.2⟩
      exact mem_iUnion.mpr ⟨z, t, by rw [← heq]; exact hL.1⟩
  let e := Fintype.equivFin B
  refine ⟨Fintype.card B, fun i => lift (e.symm i), fun i => hi _,
    fun i k hik => hdis (fun h => hik (e.symm.injective h)), ?_, fun i t => hcoord _ t⟩
  rw [← hwhole]
  apply le_antisymm
  · exact iUnion_mono' (fun i => ⟨e.symm i, subset_rfl⟩)
  · intro x hx
    obtain ⟨z, hz⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨e z, by simpa only [e.symm_apply_apply] using hz⟩

theorem exists_finite_rectangle_family
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    {p : ℝ} [Fact (0 < p)] {c : C(X, unitInterval × AddCircle p)}
    (hc : IsCoveringMap c) {u v : ℝ} (huv : u < v) (hwidth : v < u + p) :
    ∃ (n : ℕ)
      (face : Fin n → C((Icc (0 : ℝ) 1 ×ˢ Icc u v : Set (ℝ × ℝ)), X)),
      (∀ i, Topology.IsEmbedding (face i)) ∧
      Pairwise (fun i k => Disjoint (range (face i)) (range (face k))) ∧
      (⋃ i, range (face i)) = {x | (c x).2 ∈ AddCircle.closedIntervalArc p u v} ∧
      ∀ i t, c (face i t) = (⟨(t : ℝ × ℝ).1, t.property.1⟩, ((t : ℝ × ℝ).2 : AddCircle p)) := by
  let A := (Icc (0 : ℝ) 1 ×ˢ Icc u v : Set (ℝ × ℝ))
  have hconvex : Convex ℝ A := (convex_Icc (0 : ℝ) 1).prod (convex_Icc u v)
  let a0 : A := ⟨(0, u), ⟨by norm_num, le_rfl, huv.le⟩⟩
  let : ContractibleSpace A := hconvex.contractibleSpace ⟨a0, a0.property⟩
  let : LocallyPathConnectedSpace A := hconvex.locallyPathConnectedSpace
  let : CompactSpace A := isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)
  let base : C(A, unitInterval × AddCircle p) :=
    ⟨fun t => (⟨(t : ℝ × ℝ).1, t.property.1⟩, ((t : ℝ × ℝ).2 : AddCircle p)), by
      fun_prop⟩
  have hbase : Function.Injective base := by
    intro x y hxy
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z : unitInterval × AddCircle p => (z.1 : ℝ)) hxy
    · exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
        (show (x : ℝ × ℝ).2 ∈ Ico u (u + p) from
          ⟨x.property.2.1, x.property.2.2.trans_lt hwidth⟩)
        (show (y : ℝ × ℝ).2 ∈ Ico u (u + p) from
          ⟨y.property.2.1, y.property.2.2.trans_lt hwidth⟩)).mp (congrArg Prod.snd hxy)
  obtain ⟨n, face, hi, hdis, hwhole, hcoord⟩ :=
    hc.exists_finite_lifted_compact_family base hbase a0
  refine ⟨n, face, hi, hdis, hwhole.trans ?_, hcoord⟩
  ext x
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨(t : ℝ × ℝ).2, t.property.2, congrArg Prod.snd ht⟩
  · rintro ⟨t, ht, htx⟩
    refine ⟨⟨((c x).1, t), (c x).1.property, ht⟩, ?_⟩
    exact Prod.ext rfl htx

end IsCoveringMap

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Ann" => squareAnnulus 8 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem HamiltonZeroInstalledAnnulusPLArcFibers.mem_frontier_iff_cover_boundary
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3} {R : Set X0}
    {j : ℝ × ℝ → X0} {phi : C(H0, H0)}
    {c : C(Ann, unitInterval × C0)}
    (harcs : HamiltonZeroInstalledAnnulusPLArcFibers e R j phi c)
    (hc : IsCoveringMap c) (z : Ann) :
    j z ∈ frontier R ↔ (c z).1 = 0 ∨ (c z).1 = 1 := by
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  let : Fact (0 < p) := ⟨by norm_num⟩
  let : CompactSpace Ann := Dehn.annulusCylinderHomeomorph.compactSpace
  obtain ⟨n, arc, param, hi, _, _, _, hdis, hwhole, _, hmark⟩ := harcs (c z).2
  obtain ⟨i, t, ht⟩ := mem_iUnion.mp (hwhole.symm.subset (show (c z).2 = (c z).2 from rfl))
  obtain ⟨H, hH⟩ := hc.exists_fiber_parameter_homeomorph (c z).2 arc hi hdis hwhole i
  have hmark' : j z ∈ frontier R ↔ t = 0 ∨ t = 1 := by
    rw [← ht]
    exact hmark i t
  have hcoord : H t = (c z).1 := (hH t).trans (congrArg (fun x => (c x).1) ht)
  rw [hmark', ← hcoord]
  constructor
  · rintro (rfl | rfl)
    · exact interval_homeomorph_preimage_endpoint H.symm false
    · exact interval_homeomorph_preimage_endpoint H.symm true
  · rintro (ht0 | ht1)
    · have ht' : t = H.symm 0 := H.symm_apply_apply t ▸ congrArg H.symm ht0
      rw [ht']
      exact interval_homeomorph_preimage_endpoint H false
    · have ht' : t = H.symm 1 := H.symm_apply_apply t ▸ congrArg H.symm ht1
      rw [ht']
      exact interval_homeomorph_preimage_endpoint H true

theorem hamiltonZeroAnnulusTargetMap_injective
    {alpha beta delta0 delta1 : ℝ} (hwidth : beta < alpha + p)
    (h0 : delta0 ∈ Icc alpha beta) (h1 : delta1 ∈ Icc alpha beta)
    (hne : delta0 ≠ delta1) (theta : C0) :
    Function.Injective (hamiltonZeroAnnulusTargetMap delta0 delta1 theta) := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  intro x y hxy
  have hcoords := congrArg Q0 hxy
  rw [hamiltonZeroAnnulusTargetMap_coordinates,
    hamiltonZeroAnnulusTargetMap_coordinates] at hcoords
  have hrange (s : unitInterval) :
      (delta1 - delta0) * (s : ℝ) + delta0 ∈ Ico alpha (alpha + p) := by
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr h0.1) (sub_nonneg.mpr s.property.2),
        mul_nonneg (sub_nonneg.mpr h1.1) s.property.1]
    · have hle : (delta1 - delta0) * (s : ℝ) + delta0 ≤ beta := by
        nlinarith [mul_nonneg (sub_nonneg.mpr h0.2) (sub_nonneg.mpr s.property.2),
          mul_nonneg (sub_nonneg.mpr h1.2) s.property.1]
      exact hle.trans_lt hwidth
  have hnormal := (AddCircle.coe_eq_coe_iff_of_mem_Ico (hrange x.1) (hrange y.1)).mp
    (congrArg Prod.snd hcoords)
  apply Prod.ext
  · apply Subtype.ext
    exact mul_left_cancel₀ (sub_ne_zero.mpr hne.symm) (add_right_cancel hnormal)
  · exact congrArg (fun z : (C0 × C0) × C0 => z.1.1) hcoords

private theorem polyhedralPL_hamiltonZero_target_rectangle
    {κ : Type*} {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (K : SimplicialComplex ℝ (ℝ × ℝ)) (hK : K.faces.Finite)
    (delta0 delta1 : ℝ) (theta : C0) :
    PolyhedralPLInCharts d (fun z : ℝ × ℝ =>
      (Q0).symm (((z.2 : C0), theta),
        (((delta1 - delta0) * z.1 + delta0 : ℝ) : C0))) K.space := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  let thetaReal : ℝ := AddCircle.equivIco p 0 theta
  have htheta : (thetaReal : C0) = theta := AddCircle.coe_equivIco
  let linear : (ℝ × ℝ) →L[ℝ] V3 := ContinuousLinearMap.pi
    ![ContinuousLinearMap.snd ℝ ℝ ℝ, 0,
      (delta1 - delta0) • ContinuousLinearMap.fst ℝ ℝ ℝ]
  let lift : (ℝ × ℝ) →ᴬ[ℝ] ((Fin 0 ⊕ Fin 3) → ℝ) :=
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 0) (Fin 3)
      (fun _ => ℝ)).symm.toContinuousAffineEquiv.toContinuousAffineMap.comp
      ((ContinuousAffineMap.const ℝ (ℝ × ℝ) (0 : Fin 0 → ℝ)).prod
        (linear.toContinuousAffineMap +
          ContinuousAffineMap.const ℝ (ℝ × ℝ) ![0, thetaReal, delta0]))
  have hlift : FinitePiecewiseAffineOn lift K.space :=
    ⟨K, hK, rfl, K.affineOnFaces_affine lift⟩
  apply (hd.polyhedralPL_projection hlift).congr
  intro z hz
  apply (Q0).injective
  rw [(Q0).apply_symm_apply]
  change (((((z.2 + 0 : ℝ) : C0), ((0 + thetaReal : ℝ) : C0)),
    (((delta1 - delta0) * z.1 + delta0 : ℝ) : C0))) = _
  simp only [add_zero, zero_add, htheta]

theorem exists_hamiltonZero_original_annulus_rectangle_faces
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {j : ℝ × ℝ → X0} (hj : PolyhedralPLInCharts e j Ann)
    (hji : Topology.IsEmbedding (fun z : Ann => j z))
    (c : C(Ann, unitInterval × C0)) (hc : IsCoveringMap c)
    {alpha beta delta0 delta1 : ℝ} (hwidth : beta < alpha + p)
    (h0 : delta0 ∈ Icc alpha beta) (h1 : delta1 ∈ Icc alpha beta)
    (hne : delta0 ≠ delta1) (theta : C0)
    (hformula : ∀ z : Ann, hamiltonZeroAmbientMap phi (j z) =
      hamiltonZeroAnnulusTargetMap delta0 delta1 theta (c z))
    {u v : ℝ} (huv : u < v) (huvwidth : v < u + p) :
    ∃ (n : ℕ)
      (face : Fin n → C((Icc (0 : ℝ) 1 ×ˢ Icc u v : Set (ℝ × ℝ)), Ann))
      (param : Fin n → (ℝ × ℝ) → ℝ × ℝ),
      (∀ i, Topology.IsEmbedding (face i)) ∧
      (∀ i, FinitePiecewiseAffineOn (param i) (Icc (0 : ℝ) 1 ×ˢ Icc u v)) ∧
      (∀ i (t : (Icc (0 : ℝ) 1 ×ˢ Icc u v : Set (ℝ × ℝ))),
        param i t = (face i t : ℝ × ℝ)) ∧
      (∀ i, PolyhedralPLInCharts e (j ∘ param i) (Icc (0 : ℝ) 1 ×ˢ Icc u v)) ∧
      Pairwise (fun i k => Disjoint
        (range (fun t => j (face i t))) (range (fun t => j (face k t)))) ∧
      (⋃ i, range (fun t => j (face i t))) =
        j '' Ann ∩ hamiltonZeroThirdCircleMap phi ⁻¹' AddCircle.closedIntervalArc p u v ∧
      (∀ i t, c (face i t) =
        (⟨(t : ℝ × ℝ).1, t.property.1⟩, ((t : ℝ × ℝ).2 : C0))) ∧
      ∀ i t, hamiltonZeroAmbientMap phi (j (face i t)) =
        (Q0).symm ((((t : ℝ × ℝ).2 : C0), theta),
          (((delta1 - delta0) * (t : ℝ × ℝ).1 + delta0 : ℝ) : C0)) := by
  classical
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  let : Fact (0 < p) := ⟨by norm_num⟩
  let : CompactSpace Ann := Dehn.annulusCylinderHomeomorph.compactSpace
  obtain ⟨n, face, hi, hdis, hwhole, hcoord⟩ := hc.exists_finite_rectangle_family huv huvwidth
  let Rect := (Icc (0 : ℝ) 1 ×ˢ Icc u v : Set (ℝ × ℝ))
  let param (i : Fin n) (z : ℝ × ℝ) : ℝ × ℝ :=
    if hz : z ∈ Rect then face i ⟨z, hz⟩ else 0
  have hparam (i : Fin n) (t : Rect) : param i t = (face i t : ℝ × ℝ) := by
    simp only [param, dif_pos t.property]
    rfl
  obtain ⟨P, hP, hPA⟩ := _root_.Dehn.exists_finite_square_annulus_complex
    (by norm_num : (0 : ℝ) < 1) (by norm_num : 4 * (1 : ℝ) < 8)
  let Y : (ℝ × ℝ) → X0 := fun z => hamiltonZeroAmbientMap phi (j z)
  have hYP : PolyhedralPLInCharts d Y P.space :=
    hphi.polyhedralPL_hamiltonZeroAmbientMap_comp P hP
      (show PolyhedralPLInCharts e j P.space from hPA ▸ hj)
  have hYinj : IsLocallyInjective (fun x : P.space => Y x) := by
    have hAnn : IsLocallyInjective (fun x : Ann => Y x) := by
      intro x
      obtain ⟨U, hU, hxU, hcU⟩ := hc.isLocalHomeomorph.isLocallyInjective x
      refine ⟨U, hU, hxU, ?_⟩
      intro y hy z hz heq
      apply hcU hy hz
      apply hamiltonZeroAnnulusTargetMap_injective hwidth h0 h1 hne theta
      exact (hformula y).symm.trans (heq.trans (hformula z))
    change IsLocallyInjective (fun x : P.space => Y (x : ℝ × ℝ))
    rw [hPA]
    exact hAnn
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKR, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).prod
      (isFinitePLBallPair_Icc huv)
  have hparamP (i : Fin n) : MapsTo (param i) K.space P.space := by
    intro z hz
    rw [hPA, hparam i ⟨z, hKR.subset hz⟩]
    exact (face i ⟨z, hKR.subset hz⟩).property
  have hparamPL (i : Fin n) : FinitePiecewiseAffineOn (param i) Rect := by
    have hcont : ContinuousOn (param i) Rect := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact (continuous_subtype_val.comp (face i).continuous).congr (fun t => (hparam i t).symm)
    have hcomposite : PolyhedralPLInCharts d (Y ∘ param i) K.space := by
      apply (polyhedralPL_hamiltonZero_target_rectangle hd K hK delta0 delta1 theta).congr
      intro z hz
      rw [Function.comp_apply, hparam i ⟨z, hKR.subset hz⟩]
      change _ = hamiltonZeroAmbientMap phi (j (face i ⟨z, hKR.subset hz⟩))
      rw [hformula, hcoord]
      rfl
    have hPL := hYP.finitePiecewiseAffineOn_lift_of_locallyInjective
      hphi.target_domain.compatible P hP hYinj K hK
      (show ContinuousOn (param i) K.space from hKR ▸ hcont) (hparamP i) hcomposite
    simpa only [Rect, hKR] using hPL
  have hjparam (i : Fin n) : PolyhedralPLInCharts e (j ∘ param i) Rect := by
    have hPL : FinitePiecewiseAffineOn (param i) K.space := hKR ▸ hparamPL i
    have hmap : MapsTo (param i) K.space Ann := fun z hz => hPA.subset (hparamP i hz)
    simpa only [Rect, hKR] using hj.comp_finitePiecewiseAffineOn K hK hPL hmap
  have hthird (z : Ann) : hamiltonZeroThirdCircleMap phi (j z) = (c z).2 := by
    rw [hamiltonZeroThirdCircleMap_ambient, hformula, hamiltonZeroAnnulusTargetMap_coordinates]
  refine ⟨n, face, param, hi, hparamPL, hparam, hjparam, ?_, ?_, hcoord, ?_⟩
  · intro i k hik
    apply disjoint_left.mpr
    rintro x ⟨s, rfl⟩ ⟨t, hst⟩
    exact disjoint_left.mp (hdis hik) (mem_range_self s)
      ⟨t, hji.injective hst⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨i, t, rfl⟩ := mem_iUnion.mp hx
      refine ⟨⟨face i t, (face i t).property, rfl⟩, ?_⟩
      change hamiltonZeroThirdCircleMap phi (j (face i t)) ∈ AddCircle.closedIntervalArc p u v
      rw [hthird]
      exact hwhole.subset (mem_iUnion.mpr ⟨i, mem_range_self t⟩)
    · rintro ⟨⟨z, hz, rfl⟩, hphase⟩
      have hmem : (⟨z, hz⟩ : Ann) ∈ ⋃ i, range (face i) := by
        rw [hwhole]
        change (c ⟨z, hz⟩).2 ∈ AddCircle.closedIntervalArc p u v
        rwa [← hthird ⟨z, hz⟩]
      obtain ⟨i, t, ht⟩ := mem_iUnion.mp hmem
      exact mem_iUnion.mpr ⟨i, t, congrArg (fun z : Ann => j z) ht⟩
  · intro i t
    rw [hformula, hcoord]
    rfl

end PoincareConjecture.M76
