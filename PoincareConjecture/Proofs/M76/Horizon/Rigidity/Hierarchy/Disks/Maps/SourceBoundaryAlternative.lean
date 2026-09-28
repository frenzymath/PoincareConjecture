import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Maps.SourceDiskAlternative
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Maps.ExtendedFailureArc










set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Ann" => squareAnnulus 8 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates



def HamiltonZeroBoundaryFailureArc {ι : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3) (R : Set X0) (phi : C(H0, H0)) : Prop :=
  ∃ (P : ℝ → X0) (k : C(unitInterval, X0)),
    PolyhedralPLInCharts e P (Icc (0 : ℝ) 1) ∧
    (∀ t : unitInterval, P t = k t) ∧ Topology.IsEmbedding k ∧
    range k ⊆ R ∧ (∀ t, k t ∈ frontier R ↔ t = 0 ∨ t = 1) ∧
    (∀ t, k t ∈ interior R ↔ t ≠ 0 ∧ t ≠ 1) ∧
    Nonempty (((hamiltonZeroAmbientMap phi).comp k).HomotopyRel
      (ContinuousMap.const unitInterval (hamiltonZeroAmbientMap phi (k 0)))
      ({0, 1} : Set unitInterval))



theorem HamiltonZeroBoundaryFailureArc.of_exterior_homotopy
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3} {R : Set X0}
    {phi psi : C(H0, H0)}
    (G : (hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap psi) (interior R)ᶜ)
    (failure : HamiltonZeroBoundaryFailureArc e R psi) :
    HamiltonZeroBoundaryFailureArc e R phi := by
  obtain ⟨P, k, hPL, hPk, hk, hkR, hkfront, hkint, ⟨F⟩⟩ := failure
  let H : ((hamiltonZeroAmbientMap phi).comp k).HomotopyRel
      ((hamiltonZeroAmbientMap psi).comp k) ({0, 1} : Set unitInterval) := {
    toFun := fun z => G (z.1, k z.2)
    continuous_toFun := G.continuous.comp (continuous_fst.prodMk (k.continuous.comp continuous_snd))
    map_zero_left := fun t => G.apply_zero (k t)
    map_one_left := fun t => G.apply_one (k t)
    prop' := by
      intro s t ht
      exact G.eq_fst s ((hkfront t).mpr ht).2 }
  have heq : hamiltonZeroAmbientMap psi (k 0) = hamiltonZeroAmbientMap phi (k 0) :=
    (G.fst_eq_snd ((hkfront 0).mpr (Or.inl rfl)).2).symm
  refine ⟨P, k, hPL, hPk, hk, hkR, hkfront, hkint, ?_⟩
  exact ⟨(H.trans F).cast rfl (congrArg (ContinuousMap.const unitInterval) heq)⟩



theorem hamiltonZero_boundary_failure_of_installed_folded_annulus
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3} {R : Set X0}
    (phi : C(H0, H0)) (hR : IsClosed R)
    (j : ℝ × ℝ → X0) (hj : Topology.IsEmbedding (fun z : Ann => j z))
    (hjR : j '' Ann ⊆ R) (c : C(Ann, unitInterval × C0))
    (harcs : HamiltonZeroInstalledAnnulusPLArcFibers e R j phi c)
    (delta : ℝ) (theta : C0)
    (hformula : ∀ z : Ann, hamiltonZeroAmbientMap phi (j z) =
      hamiltonZeroAnnulusTargetMap delta delta theta (c z)) :
    HamiltonZeroBoundaryFailureArc e R phi := by
  let z : Ann := Dehn.annulusRimPoint false 0
  let xi := (c z).2
  obtain ⟨n, arc, param, hi, hPL, hparam, hjparam, _, hwhole, _, hmark⟩ := harcs xi
  obtain ⟨i, _, _⟩ := mem_iUnion.mp (hwhole.symm.subset (show (c z).2 = xi from rfl))
  let k : C(unitInterval, X0) := ⟨fun t => j (arc i t), hj.continuous.comp (arc i).continuous⟩
  have hphase (t : unitInterval) : (c (arc i t)).2 = xi :=
    hwhole.subset (mem_iUnion.mpr ⟨i, t, rfl⟩)
  have hconstant (t : unitInterval) : hamiltonZeroAmbientMap phi (k t) =
      (Q0).symm ((xi, theta), (delta : C0)) := by
    change hamiltonZeroAmbientMap phi (j (arc i t)) = _
    rw [hformula]
    simp only [hamiltonZeroAnnulusTargetMap, ContinuousMap.coe_mk, sub_self,
      zero_mul, zero_add, hphase]
  have hkR : range k ⊆ R := by
    rintro _ ⟨t, rfl⟩
    exact hjR ⟨arc i t, (arc i t).property, rfl⟩
  have hkfront (t : unitInterval) : k t ∈ frontier R ↔ t = 0 ∨ t = 1 := hmark i t
  have hkint (t : unitInterval) : k t ∈ interior R ↔ t ≠ 0 ∧ t ≠ 1 := by
    have hm := hkR ⟨t, rfl⟩
    have hf : k t ∈ frontier R ↔ k t ∉ interior R := by
      rw [hR.frontier_eq]
      exact and_iff_right hm
    rw [← not_or, ← hkfront, hf, not_not]
  have heq : (hamiltonZeroAmbientMap phi).comp k =
      ContinuousMap.const unitInterval (hamiltonZeroAmbientMap phi (k 0)) := by
    apply ContinuousMap.ext
    intro t
    exact (hconstant t).trans (hconstant 0).symm
  exact ⟨j ∘ param i, k, hjparam i, fun t => congrArg j (hparam i t),
    hj.comp (hi i), hkR, hkfront, hkint,
    ⟨(ContinuousMap.HomotopyRel.refl ((hamiltonZeroAmbientMap phi).comp k) _).cast rfl heq⟩⟩


def HamiltonZeroTerminalHomeomorphicDisks {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3) (d : κ → OpenPartialHomeomorph X0 V3)
    (R : Set X0) (phi : C(H0, H0)) (u v alpha beta a b : ℝ) : Prop :=
  ∃ (n : Bool → ℕ) (j : (Σ s : Bool, Fin (n s)) → V2 → X0),
    (∀ s : Bool, (⋃ i : Fin (n s), j ⟨s, i⟩ '' Disk) =
      R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {((if s then v else u : ℝ) : C0)}) ∧
    Pairwise (fun i k => Disjoint (j i '' Disk) (j k '' Disk)) ∧
    (∀ i, PolyhedralPLInCharts e (j i) Disk ∧
      Topology.IsEmbedding (fun z : Disk => j i z) ∧ MapsTo (j i) Disk R ∧
      (∀ z : Disk, j i z ∈ frontier R ↔ (z : V2) ∈ Rim) ∧
      IsCompact (j i '' Disk) ∧ IsPathConnected (j i '' Disk) ∧
      ∀ x ∈ j i '' Disk, connectedComponentIn
        (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {((if i.1 then v else u : ℝ) : C0)}) x =
          j i '' Disk) ∧
    HamiltonZeroHomeomorphicDiskInstallation e d R phi j
      (fun i => ((if i.1 then v else u : ℝ) : C0)) alpha beta a b



def HamiltonZeroSourceBoundaryDiskData {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3) (d : κ → OpenPartialHomeomorph X0 V3)
    (phi : C(H0, H0)) (R : Set X0) (alpha beta : ℝ) : Prop :=
  ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
    (∀ theta ∈ ({a, b} : Set ℝ), HamiltonZeroSecondCoordinateRegularity e R phi (theta : C0)) ∧
    ∃ (chi eta : C(H0, H0)) (A : Set X0)
      (n : Bool → ℕ) (j : (Σ s : Bool, Fin (n s)) → ℝ × ℝ → X0)
      (delta0 delta1 : (Σ s : Bool, Fin (n s)) → ℝ)
      (f : (Σ s : Bool, Fin (n s)) → C(Ann, unitInterval × C0)),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 chi) ∧
      Nonempty (phi.HomotopyRel chi B0) ∧ Nonempty ((ContinuousMap.id H0).HomotopyRel chi B0) ∧
      Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap chi) (interior R)ᶜ) ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 eta) ∧
      Nonempty (chi.HomotopyRel eta B0) ∧ Nonempty (phi.HomotopyRel eta B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel eta B0) ∧
      Nonempty ((hamiltonZeroAmbientMap chi).HomotopyRel (hamiltonZeroAmbientMap eta) (interior R)ᶜ) ∧
      IsCompact A ∧ A ⊆ interior R ∧
      (∀ x ∉ A, hamiltonZeroAmbientMap eta x = hamiltonZeroAmbientMap chi x) ∧
      hamiltonZeroCircleMap eta = hamiltonZeroCircleMap chi ∧
      hamiltonZeroSecondCircleMap eta = hamiltonZeroSecondCircleMap chi ∧
      R ⊆ hamiltonZeroCircleMap chi ⁻¹' AddCircle.closedIntervalArc p alpha beta ∧
      frontier R ⊆ hamiltonZeroCircleMap chi ⁻¹' {(alpha : C0), (beta : C0)} ∧
      HamiltonZeroSecondPhaseGeometry e R chi a b ∧
      (∀ s : Bool, IsPLIrreducible e (R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
        AddCircle.closedIntervalArc p (if s then b else a) (if s then a + p else b))) ∧
      (∀ s : Bool,
        let N := R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
          AddCircle.closedIntervalArc p (if s then b else a) (if s then a + p else b)
        ∀ x : N, Function.Injective
          (FundamentalGroup.map (ContinuousMap.inclusion (inter_subset_left : N ⊆ R)) x)) ∧
      (∀ theta : C0, (frontier R ∩ hamiltonZeroSecondCircleMap chi ⁻¹' {theta}).Nonempty) ∧
      (∀ s : Bool, (⋃ i : Fin (n s), j ⟨s, i⟩ '' Ann) =
        R ∩ hamiltonZeroSecondCircleMap chi ⁻¹' {((if s then b else a : ℝ) : C0)}) ∧
      Pairwise (fun i k => Disjoint (j i '' Ann) (j k '' Ann)) ∧
      (∀ i, PolyhedralPLInCharts e (j i) Ann ∧
        Topology.IsEmbedding (fun z : Ann => j i z) ∧
        (∀ z : Ann, depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1 ↔
          j i z ∈ frontier R) ∧
        delta0 i ∈ ({alpha, beta} : Set ℝ) ∧ delta1 i ∈ ({alpha, beta} : Set ℝ) ∧
        delta0 i ≠ delta1 i ∧ IsCoveringMap (f i) ∧
        (∀ z : Ann, hamiltonZeroAmbientMap chi (j i z) =
          hamiltonZeroAnnulusTargetMap (delta0 i) (delta1 i)
            ((if i.1 then b else a : ℝ) : C0) (f i z)) ∧
        HamiltonZeroInstalledAnnulusPLArcFibers e R (j i) chi (f i)) ∧
      (∀ s : Bool, EqOn (hamiltonZeroAmbientMap eta) (hamiltonZeroAmbientMap chi)
        (frontier (R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
          AddCircle.closedIntervalArc p (if s then b else a) (if s then a + p else b)))) ∧
      ∀ s : Bool,
        let N := R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
          AddCircle.closedIntervalArc p (if s then b else a) (if s then a + p else b)
        ∃ u ∈ Ioo (p / 4) (p / 3), ∃ v ∈ Ioo (2 * p / 3) (3 * p / 4),
          (∀ t ∈ ({u, v} : Set ℝ), HamiltonZeroThirdCoordinateRegularity e N chi (t : C0)) ∧
          HamiltonZeroTerminalThirdPhaseData e N eta u v ∧
          HamiltonZeroSupportedThirdRealization e d chi N eta u v ∧
          (∀ thirdSide : Bool,
            let T := N ∩ hamiltonZeroThirdCircleMap eta ⁻¹'
              AddCircle.closedIntervalArc p (if thirdSide then v else u) (if thirdSide then u + p else v)
            ∀ x : T, Subsingleton (FundamentalGroup T x)) ∧
          HamiltonZeroTerminalHomeomorphicDisks e d N eta u v alpha beta
            (if s then b else a) (if s then a + p else b)

theorem exists_hamiltonZero_source_boundary_disk_alternative
    {E ι κ : Type*} [TopologicalSpace E] [Zero E]
    (e : ι → OpenPartialHomeomorph X0 V3) (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F0 : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} (hI : IsPLIrreducible e R)
    {cut alpha beta : ℝ}
    (ha : cut < alpha) (hab : alpha < beta) (hb : beta < cut + p)
    (hR : R ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hRfront : frontier R ⊆ hamiltonZeroCircleMap phi ⁻¹' {(alpha : C0), (beta : C0)})
    (hinjR : ∀ x : R, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(R, X0)) x))
    {K : Set E} (hK : IsCompact K) (hne : K.Nonempty) {r : ℝ} (hr : 0 < r)
    (c : E × ℝ → X0)
    (hc : ContinuousOn c (K ×ˢ Icc (-r) r))
    (hi : Topology.IsEmbedding (fun z : (K ×ˢ Icc (-r) r : Set (E × ℝ)) => c z))
    (ho : IsOpen (c '' (K ×ˢ Ioo (-r) r)))
    (hzero : c '' (K ×ˢ ({0} : Set ℝ)) = frontier R)
    (hside : ∀ z ∈ K ×ˢ Icc (-r) r, c z ∈ R ↔ 0 ≤ z.2)
    (g : C(K, C0 × C0)) (hg : IsCoveringMap g)
    (hproduct : ∀ x : K, ∀ t ∈ Icc (-r) r,
      (Q0 (hamiltonZeroAmbientMap phi (c (x, t)))).1 = g x) :
    HamiltonZeroSourceBoundaryDiskData e d phi R alpha beta ∨
      HamiltonZeroBoundaryFailureArc e R phi := by
  classical
  let : Fact (0 < p) := ⟨by norm_num⟩
  obtain ⟨a, ha', b, hb', hreg, chi, n, j, hchi, ⟨Hchi⟩, ⟨Fchi⟩, ⟨Gchi⟩,
      hRchi, geometry, hcuts, hinj, hboundary, hfamily, hdis, hprops⟩ :=
    exists_hamiltonZero_source_annulus_family_installation e d hd phi hphi F0 hI
      ha hab hb hR hRfront hinjR hK hne hr c hc hi ho hzero hside g hg hproduct
  choose delta0 hd0 delta1 hd1 f hf hvalue harcs using fun i => (hprops i).2.2.2
  have hjR (i : Σ s : Bool, Fin (n s)) : j i '' Ann ⊆ R := by
    have hsub := subset_iUnion (fun k : Fin (n i.1) => j ⟨i.1, k⟩ '' Ann) i.2
    rw [hfamily] at hsub
    exact hsub.trans inter_subset_left
  by_cases hfold : ∃ i, delta0 i = delta1 i
  · obtain ⟨i, hfold⟩ := hfold
    right
    apply HamiltonZeroBoundaryFailureArc.of_exterior_homotopy Gchi
    exact hamiltonZero_boundary_failure_of_installed_folded_annulus chi hI.1.closed
      (j i) (hprops i).2.1 (hjR i) (f i) (harcs i) (delta0 i)
      ((if i.1 then b else a : ℝ) : C0) (fun z => by
        simpa only [← hfold] using hvalue i z)
  have hnofold : ∀ i, delta0 i ≠ delta1 i := fun i h => hfold ⟨i, h⟩
  have ha0 : 0 < a := by linarith [ha'.1]
  have hab0 : a < b := by linarith [ha'.2, hb'.1]
  have hb0 : b < p := by linarith [hb'.2]
  have hfrontChi : frontier R ⊆ hamiltonZeroCircleMap chi ⁻¹' {(alpha : C0), (beta : C0)} := by
    intro x hx
    rw [mem_preimage, ← hamiltonZeroAmbientMap_circle, ← Gchi.fst_eq_snd hx.2,
      hamiltonZeroAmbientMap_circle]
    exact hRfront hx
  have hlocal := hamiltonZero_installed_second_slabs_terminal_third_hierarchies e d hd
    chi hchi Fchi hI.1 hinjR ha0 hab0 hb0 geometry hcuts hinj (hboundary a) n j hfamily
    (fun i => ⟨delta0 i, delta1 i, f i, hf i, hvalue i⟩) ha hb hRchi
  obtain ⟨eta, A, hA, hAR, hfixed, heta, ⟨Heta⟩, ⟨Feta⟩, ⟨Geta⟩,
      hfirst, hsecond, terminal⟩ :=
    exists_hamiltonZero_simultaneous_terminal_second_slab_hierarchies chi Fchi
      ha0 hab0 hb0 geometry hlocal
  let N := fun s : Bool => R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
    AddCircle.closedIntervalArc p (if s then b else a) (if s then a + p else b)
  choose u hu v hv hregThird hterminal hreal using terminal
  have hN (s : Bool) : PLDomain e (N s) := (geometry.slabs s).1
  have hfrontEq (s : Bool) :
      EqOn (hamiltonZeroAmbientMap eta) (hamiltonZeroAmbientMap chi) (frontier (N s)) := by
    obtain ⟨localMap, _, _, _, _, _, _, _, _, _, ⟨Glocal⟩, _, heq⟩ := hreal s
    intro x hx
    exact (heq ((hN s).closed.frontier_subset hx)).trans (Glocal.fst_eq_snd hx.2).symm
  have hinjN (s : Bool) : ∀ x : N s, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(N s, X0)) x) := by
    let incl := ContinuousMap.inclusion (inter_subset_left : N s ⊆ R)
    let ambient : C(R, X0) := ⟨Subtype.val, continuous_subtype_val⟩
    intro x
    change Function.Injective (FundamentalGroup.map (ambient.comp incl) x)
    rw [FundamentalGroup.map_comp]
    exact (hinjR (incl x)).comp (hinj s x)
  have harclow (s : Bool) : (if s then (a + b) / 2 else 0) < (if s then b else a) := by
    cases s <;> dsimp <;> linarith
  have harcorder (s : Bool) : (if s then b else a) < (if s then a + p else b) := by
    cases s <;> dsimp <;> linarith
  have harchigh (s : Bool) : (if s then a + p else b) < (if s then (a + b) / 2 else 0) + p := by
    cases s <;> dsimp <;> linarith
  have hfirstN (s : Bool) :
      N s ⊆ hamiltonZeroCircleMap eta ⁻¹' AddCircle.closedIntervalArc p alpha beta := by
    rw [hfirst]
    exact inter_subset_left.trans hRchi
  have hsecondN (s : Bool) : N s ⊆ hamiltonZeroSecondCircleMap eta ⁻¹'
      AddCircle.closedIntervalArc p (if s then b else a) (if s then a + p else b) := by
    rw [hsecond]
    exact inter_subset_right
  have hgroups (s : Bool) :
      ∀ t : Bool,
        let T := N s ∩ hamiltonZeroThirdCircleMap eta ⁻¹'
          AddCircle.closedIntervalArc p (if t then v s else u s) (if t then u s + p else v s)
        ∀ x : T, Subsingleton (FundamentalGroup T x) :=
    (hreal s).slabs_pi1_subsingleton (hN s) (hinjN s)
      (by linarith [(hu s).1]) (by linarith [(hu s).2, (hv s).1])
      (by linarith [(hv s).2]) (hregThird s) ha hb (harclow s) (harchigh s)
      (inter_subset_left.trans hRchi) inter_subset_right
  have hedges (s : Bool) (x : X0) (hx : x ∈ frontier (N s)) :
      hamiltonZeroCircleMap eta x ∈ ({(alpha : C0), (beta : C0)} : Set C0) ∨
      hamiltonZeroSecondCircleMap eta x ∈
        ({((if s then b else a : ℝ) : C0), ((if s then a + p else b : ℝ) : C0)} : Set C0) := by
    have hq1 : hamiltonZeroCircleMap eta x = hamiltonZeroCircleMap chi x :=
      congrArg (fun y => (Q0 y).2) (hfrontEq s hx)
    have hq2 : hamiltonZeroSecondCircleMap eta x = hamiltonZeroSecondCircleMap chi x :=
      congrArg (fun y => (Q0 y).1.2) (hfrontEq s hx)
    rw [hq1, hq2]
    exact geometry.frontier_rectangle_edges hfrontChi s x hx
  have hwhole : (⋃ i : Σ s : Bool, Fin (n s), j i '' Ann) =
      (R ∩ hamiltonZeroSecondCircleMap chi ⁻¹' {(a : C0)}) ∪
        (R ∩ hamiltonZeroSecondCircleMap chi ⁻¹' {(b : C0)}) := by
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
  have halternative (s : Bool) :
      HamiltonZeroTerminalHomeomorphicDisks e d (N s) eta (u s) (v s) alpha beta
        (if s then b else a) (if s then a + p else b) ∨
      HamiltonZeroBoundaryFailureArc e R eta := by
    have huv : ((u s) : C0) ≠ ((v s) : C0) := by
      intro heq
      have heq' := (AddCircle.coe_eq_coe_iff_of_mem_Ico
        (show u s ∈ Ico (0 : ℝ) (0 + p) by constructor <;> linarith [(hu s).1, (hu s).2])
        (show v s ∈ Ico (0 : ℝ) (0 + p) by constructor <;> linarith [(hv s).1, (hv s).2])).mp heq
      linarith [(hu s).2, (hv s).1]
    obtain ⟨m, disk, hcoverDisk, hdisDisk, hpropsDisk, good | bad⟩ :=
      (hterminal s).disk_alternative hd heta Feta (hN s) huv ha hab hb
        (harclow s) (harcorder s) (harchigh s) (hfirstN s) (hsecondN s) (hedges s)
    · exact Or.inl ⟨m, disk, hcoverDisk, hdisDisk, hpropsDisk, good⟩
    · obtain ⟨i, hi⟩ := bad
      obtain ⟨P, k, hPL, hPk, hk, hkR, hkfront, hkint, F, _⟩ :=
        exists_hamiltonZero_extended_disk_failure_arc chi eta hI.1 (hN s).closed
          inter_subset_left j (by rw [hwhole]; exact (geometry.slabs s).2.1)
          hdis (fun i => (hprops i).2.1) delta0 delta1
          (fun i => ((if i.1 then b else a : ℝ) : C0)) f hf hvalue harcs
          (hfrontEq s) ha hab hb (harclow s) (harchigh s) hd0 hd1 hnofold hfrontChi
          (disk i) ((if i.1 then v s else u s : ℝ) : C0) hi
      exact Or.inr ⟨P, k, hPL, hPk, hk, hkR, hkfront, hkint, ⟨F⟩⟩
  by_cases hgood : ∀ s : Bool,
      HamiltonZeroTerminalHomeomorphicDisks e d (N s) eta (u s) (v s) alpha beta
        (if s then b else a) (if s then a + p else b)
  · left
    refine ⟨a, ha', b, hb', hreg, chi, eta, A, n, j, delta0, delta1, f,
      hchi, ⟨Hchi⟩, ⟨Fchi⟩, ⟨Gchi⟩, heta, ⟨Heta⟩, ⟨Hchi.trans Heta⟩, ⟨Feta⟩,
      ⟨Geta⟩, hA, hAR, hfixed, hfirst, hsecond, hRchi, hfrontChi,
      geometry, hcuts, hinj, hboundary, hfamily, hdis, ?_, hfrontEq, ?_⟩
    · intro i
      exact ⟨(hprops i).1, (hprops i).2.1, (hprops i).2.2.1,
        hd0 i, hd1 i, hnofold i, hf i, hvalue i, harcs i⟩
    · intro s
      exact ⟨u s, hu s, v s, hv s, hregThird s, hterminal s, hreal s, hgroups s, hgood s⟩
  · push Not at hgood
    obtain ⟨s, hs⟩ := hgood
    exact Or.inr (((halternative s).resolve_left hs).of_exterior_homotopy (Gchi.trans Geta))

end PoincareConjecture.M76
