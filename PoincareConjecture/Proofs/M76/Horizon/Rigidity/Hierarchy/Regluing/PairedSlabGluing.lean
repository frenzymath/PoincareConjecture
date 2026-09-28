import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.TerminalLocalGluing
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Maps.SourceDiskAlternative
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Coverings.ThirdPhaseArcs
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.FiniteClosedPartition
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.LocalPLInterior
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.CompactDomainRestriction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Arcs.Mathlib.ShiftedCircleClosedArc

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76

theorem ChartwisePLMap.mem_frontier_of_short_circle_endpoint
    {X Y ι κ : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {d : κ → OpenPartialHomeomorph Y (Fin 3 → ℝ)}
    {P : Set X} {T : Set Y} {f : C(P, T)} (hf : ChartwisePLMap e d f)
    (hinj : IsLocallyInjective f)
    {p : ℝ} [Fact (0 < p)] (phase : C(Y, AddCircle p)) (hopen : IsOpenMap phase)
    {a b : ℝ} (hab : a ≤ b) (hw : b < a + p)
    (hmap : ∀ x : P, phase (f x) ∈ AddCircle.closedIntervalArc p a b)
    (x : P) (hend : phase (f x) ∈ ({(a : AddCircle p), (b : AddCircle p)} : Set (AddCircle p))) :
    (x : X) ∈ frontier P := by
  apply (mem_frontier_iff_notMem_interior x.property).mpr
  intro hx
  have htarget : (f x : Y) ∈ interior (phase ⁻¹' AddCircle.closedIntervalArc p a b) :=
    interior_mono (by rintro _ ⟨y, rfl⟩; exact hmap y)
      (hf.mem_interior_image_of_locallyInjective hinj x hx)
  have hfront : (f x : Y) ∈ frontier (phase ⁻¹' AddCircle.closedIntervalArc p a b) := by
    rw [← hopen.preimage_frontier_eq_frontier_preimage phase.continuous,
      AddCircle.frontier_closedIntervalArc_shifted p (c := (a + b - p) / 2)
        (by linarith) hab (by linarith)]
    exact hend
  exact hfront.2 htarget

theorem complementary_closed_circle_arcs_inter
    (p : ℝ) [Fact (0 < p)] {a b : ℝ} (hab : a < b) (hw : b < a + p) :
    AddCircle.closedIntervalArc p a b ∩ AddCircle.closedIntervalArc p b (a + p) =
      {(a : AddCircle p), (b : AddCircle p)} := by
  ext x
  constructor
  · rintro ⟨⟨s, hs, hsx⟩, ⟨t, ht, htx⟩⟩
    by_cases htop : t = a + p
    · exact Or.inl (htx.symm.trans (htop ▸ AddCircle.coe_add_period p a))
    · have htI : t ∈ Ico a (a + p) := ⟨hab.le.trans ht.1, lt_of_le_of_ne ht.2 htop⟩
      have hsI : s ∈ Ico a (a + p) := ⟨hs.1, hs.2.trans_lt hw⟩
      have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico hsI htI).mp (hsx.trans htx.symm)
      have hsb : s = b := le_antisymm hs.2 (heq ▸ ht.1)
      exact Or.inr (hsx.symm.trans (congrArg (fun r : ℝ => (r : AddCircle p)) hsb))
  · rintro (rfl | rfl)
    · exact ⟨⟨a, ⟨le_rfl, hab.le⟩, rfl⟩,
        ⟨a + p, ⟨hw.le, le_rfl⟩, AddCircle.coe_add_period p a⟩⟩
    · exact ⟨⟨b, ⟨hab.le, le_rfl⟩, rfl⟩, ⟨b, ⟨le_rfl, hw.le⟩, rfl⟩⟩

theorem complementary_closed_circle_arcs_union
    (p : ℝ) [Fact (0 < p)] (a b : ℝ) :
    AddCircle.closedIntervalArc p a b ∪ AddCircle.closedIntervalArc p b (a + p) = univ := by
  apply eq_univ_of_forall
  intro x
  let t := AddCircle.equivIco p a x
  have ht : (t : ℝ) ∈ Ico a (a + p) := t.property
  have htx : ((t : ℝ) : AddCircle p) = x := AddCircle.coe_equivIco
  by_cases htb : (t : ℝ) ≤ b
  · exact Or.inl ⟨t, ⟨ht.1, htb⟩, htx⟩
  · exact Or.inr ⟨t, ⟨(lt_of_not_ge htb).le, ht.2.le⟩, htx⟩

theorem isLocallyInjective_of_complementary_marked_slabs
    {X Y : Type*} [TopologicalSpace X] {p : ℝ} [Fact (0 < p)]
    {S P Q B : Set X} (hP : IsClosed P) (hQ : IsClosed Q) (hcover : S ⊆ P ∪ Q)
    {a b : ℝ} (hab : a < b) (hw : b < a + p)
    (f : X → Y) (phase : Y → AddCircle p)
    (hmapP : MapsTo (phase ∘ f) P (AddCircle.closedIntervalArc p a b))
    (hmapQ : MapsTo (phase ∘ f) Q (AddCircle.closedIntervalArc p b (a + p)))
    (hmark : ∀ x ∈ P,
      phase (f x) ∈ ({(a : AddCircle p), (b : AddCircle p)} : Set (AddCircle p)) → x ∈ B)
    (hBQ : B ⊆ Q)
    (hinjP : IsLocallyInjective (fun x : P => f x))
    (hinjQ : IsLocallyInjective (fun x : Q => f x)) :
    IsLocallyInjective (fun x : S => f x) := by
  apply isLocallyInjective_of_saturated_closed_attachment hP hQ hcover hinjP hinjQ
  intro x hx y hy hxQ hxy
  rcases hcover hy with hyP | hyQ
  · apply hBQ (hmark y hyP ?_)
    rw [← complementary_closed_circle_arcs_inter p hab hw]
    exact ⟨hmapP hyP, hxy ▸ hmapQ hxQ⟩
  · exact hyQ

theorem isLocallyInjective_on_literal_complementary_slabs
    {X Y : Type*} [TopologicalSpace X] {p : ℝ} [Fact (0 < p)]
    {R : Set X} (hR : IsClosed R) (q : C(X, AddCircle p))
    {a b : ℝ} (hab : a < b) (hw : b < a + p)
    (f : X → Y) (phase : Y → AddCircle p)
    (hphase : ∀ x ∈ R, phase (f x) = q x)
    (hinj : ∀ side : Bool, IsLocallyInjective
      (fun x : ↥(R ∩ q ⁻¹' AddCircle.closedIntervalArc p
        (if side then b else a) (if side then a + p else b) : Set X) => f x)) :
    IsLocallyInjective (fun x : R => f x) := by
  have hwhole : R ⊆ q ⁻¹' AddCircle.closedIntervalArc p a b ∪
      q ⁻¹' AddCircle.closedIntervalArc p b (a + p) := by
    intro x _
    exact (complementary_closed_circle_arcs_union p a b).symm.subset (mem_univ (q x))
  apply isLocallyInjective_of_complementary_marked_slabs
    (hR.inter ((AddCircle.isCompact_closedIntervalArc p a b).isClosed.preimage q.continuous))
    (hR.inter ((AddCircle.isCompact_closedIntervalArc p b (a + p)).isClosed.preimage q.continuous))
    (fun x hx => (hwhole hx).elim (fun h => Or.inl ⟨hx, h⟩) (fun h => Or.inr ⟨hx, h⟩))
    hab hw f phase (B := R ∩ q ⁻¹' {(a : AddCircle p), (b : AddCircle p)})
  · intro x hx
    change phase (f x) ∈ _
    rw [hphase x hx.1]
    exact hx.2
  · intro x hx
    change phase (f x) ∈ _
    rw [hphase x hx.1]
    exact hx.2
  · intro x hx he
    refine ⟨hx.1, ?_⟩
    change q x ∈ ({(a : AddCircle p), (b : AddCircle p)} : Set (AddCircle p))
    rwa [hphase x hx.1] at he
  · intro x hx
    exact ⟨hx.1, ((complementary_closed_circle_arcs_inter p hab hw).symm.subset hx.2).2⟩
  · exact hinj false
  · exact hinj true

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Ann" => squareAnnulus 8 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem hamiltonZero_mem_frontier_of_locally_injective_phase_endpoint
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 (Fin 3 → ℝ)}
    {d : κ → OpenPartialHomeomorph X0 (Fin 3 → ℝ)} {psi : C(H0, H0)}
    (hpsi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi))
    {P : Set X0} (he : PLDomain e P) (hP : IsCompact P)
    (hinj : IsLocallyInjective (fun x : P => hamiltonZeroAmbientMap psi x))
    (phase : C(X0, C0)) (hopen : IsOpenMap phase)
    {a b : ℝ} (hab : a ≤ b) (hw : b < a + p)
    (hmap : MapsTo (phase ∘ hamiltonZeroAmbientMap psi) P (AddCircle.closedIntervalArc p a b))
    {x : X0} (hx : x ∈ P)
    (hend : phase (hamiltonZeroAmbientMap psi x) ∈ ({(a : C0), (b : C0)} : Set C0)) :
    x ∈ frontier P := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  have hPR : P ⊆ latticeHandleDomain (Fin 0) (Fin 3) L0 := by
    rw [hamiltonZeroDomain_eq_univ]
    exact subset_univ _
  have hf := hpsi.restrict_compact_domain he hP ⟨x, hx⟩ hPR
  have hi : IsLocallyInjective
      ((latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi).comp
        (ContinuousMap.inclusion hPR)) := by
    intro y
    obtain ⟨U, hU, hy, hi⟩ := hinj y
    exact ⟨U, hU, hy, fun z hz w hw hzw => hi hz hw (congrArg Subtype.val hzw)⟩
  exact hf.mem_frontier_of_short_circle_endpoint hi phase hopen hab hw
    (fun y => hmap y.property) ⟨x, hx⟩ hend

theorem hamiltonZero_locally_injective_of_complementary_slabs
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 (Fin 3 → ℝ)}
    {d : κ → OpenPartialHomeomorph X0 (Fin 3 → ℝ)} {chi psi : C(H0, H0)}
    (hpsi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi))
    {R : Set X0} (hR : IsClosed R)
    (phase : C(X0, C0)) (hopen : IsOpenMap phase)
    {a b : ℝ} (hab : a < b) (hw : b < a + p) :
    let q := phase.comp (hamiltonZeroAmbientMap chi)
    let N := fun side : Bool => R ∩ q ⁻¹' AddCircle.closedIntervalArc p
      (if side then b else a) (if side then a + p else b)
    PLDomain e (N false) →
    EqOn (hamiltonZeroAmbientMap psi) (hamiltonZeroAmbientMap chi) (frontier (N false)) →
    (∀ side : Bool, MapsTo (phase ∘ hamiltonZeroAmbientMap psi) (N side)
      (AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b))) →
    (∀ side : Bool, IsLocallyInjective (fun x : N side => hamiltonZeroAmbientMap psi x)) →
    IsLocallyInjective (fun x : R => hamiltonZeroAmbientMap psi x) := by
  intro q N he hfixed hmap hinj
  let : Fact (0 < p) := ⟨by norm_num⟩
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let : CompactSpace X0 := (Q0).symm.compactSpace
  have hclosed (side : Bool) : IsClosed (N side) :=
    hR.inter ((AddCircle.isCompact_closedIntervalArc p _ _).isClosed.preimage q.continuous)
  have hcover : R ⊆ N false ∪ N true := by
    intro x hx
    have h := (complementary_closed_circle_arcs_union p a b).symm.subset (mem_univ (q x))
    exact h.elim (fun h => Or.inl ⟨hx, h⟩) (fun h => Or.inr ⟨hx, h⟩)
  apply isLocallyInjective_of_complementary_marked_slabs (hclosed false) (hclosed true)
    hcover hab hw (hamiltonZeroAmbientMap psi) phase (hmap false) (hmap true)
    (B := N true) ?_ Subset.rfl (hinj false) (hinj true)
  intro x hx hend
  have hxfront := hamiltonZero_mem_frontier_of_locally_injective_phase_endpoint
    hpsi he (hclosed false).isCompact (hinj false) phase hopen hab.le hw (hmap false) hx hend
  rw [hfixed hxfront] at hend
  refine ⟨hx.1, ?_⟩
  exact ((complementary_closed_circle_arcs_inter p hab hw).symm.subset hend).2

theorem hamiltonZero_nonfolded_annulus_target_injective
    {alpha beta delta0 delta1 : ℝ} (hwidth : beta < alpha + p)
    (h0 : delta0 ∈ Icc alpha beta) (h1 : delta1 ∈ Icc alpha beta)
    (hne : delta0 ≠ delta1) (theta : C0) :
    Function.Injective (hamiltonZeroAnnulusTargetMap delta0 delta1 theta) := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  have hrange (t : unitInterval) : (delta1 - delta0) * (t : ℝ) + delta0 ∈ Ico alpha (alpha + p) := by
    have h := (convex_Icc alpha beta) h0 h1 (sub_nonneg.mpr t.property.2)
      t.property.1 (by ring : 1 - (t : ℝ) + (t : ℝ) = 1)
    simp only [smul_eq_mul] at h
    refine ⟨by nlinarith [h.1], ?_⟩
    have hle : (delta1 - delta0) * (t : ℝ) + delta0 ≤ beta := by nlinarith [h.2]
    exact hle.trans_lt hwidth
  intro x y hxy
  have hcoords := congrArg Q0 hxy
  rw [hamiltonZeroAnnulusTargetMap_coordinates, hamiltonZeroAnnulusTargetMap_coordinates] at hcoords
  have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico (hrange x.1) (hrange y.1)).mp
    (congrArg Prod.snd hcoords)
  refine Prod.ext (Subtype.ext ?_) (congrArg (fun z : (C0 × C0) × C0 => z.1.1) hcoords)
  exact mul_left_cancel₀ (sub_ne_zero.mpr hne.symm) (add_right_cancel heq)

theorem hamiltonZero_nonfolded_annuli_locally_injective
    {η : Type*} [Finite η] (phi : C(H0, H0))
    (j : η → ℝ × ℝ → X0)
    (hj : ∀ i, Continuous (fun z : Ann => j i z))
    (hi : ∀ i, Topology.IsEmbedding (fun z : Ann => j i z))
    (hdis : Pairwise (fun i k => Disjoint (j i '' Ann) (j k '' Ann)))
    (c : η → C(Ann, unitInterval × C0)) (hc : ∀ i, IsCoveringMap (c i))
    (delta0 delta1 : η → ℝ) (theta : η → C0)
    {alpha beta : ℝ} (hwidth : beta < alpha + p)
    (h0 : ∀ i, delta0 i ∈ Icc alpha beta) (h1 : ∀ i, delta1 i ∈ Icc alpha beta)
    (hne : ∀ i, delta0 i ≠ delta1 i)
    (hformula : ∀ i (z : Ann), hamiltonZeroAmbientMap phi (j i z) =
      hamiltonZeroAnnulusTargetMap (delta0 i) (delta1 i) (theta i) (c i z)) :
    IsLocallyInjective (fun x : (⋃ i, j i '' Ann) => hamiltonZeroAmbientMap phi x) := by
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  let : CompactSpace Ann := Dehn.annulusCylinderHomeomorph.compactSpace
  have hrange (i : η) : range (fun z : Ann => j i z) = j i '' Ann := by
    ext x
    simp only [mem_range, mem_image, Subtype.exists]
    constructor
    · rintro ⟨z, hz, hzx⟩
      exact ⟨z, hz, hzx⟩
    · rintro ⟨z, hz, hzx⟩
      exact ⟨z, hz, hzx⟩
  have hclosed (i : η) : IsClosed (j i '' Ann) := by
    rw [← hrange i]
    exact (isCompact_range (hj i)).isClosed
  apply isLocallyInjective_on_finite_disjoint_closed_faces (fun i => j i '' Ann) hclosed hdis
  intro i
  let H := (hi i).toHomeomorph.trans (Homeomorph.setCongr (hrange i))
  have hH (z : Ann) : (H z : X0) = j i z := rfl
  intro x
  obtain ⟨U, hU, hxU, hUinj⟩ := (hc i).isLocalHomeomorph.isLocallyInjective (H.symm x)
  refine ⟨H.symm ⁻¹' U, hU.preimage H.symm.continuous, hxU, ?_⟩
  intro y hy z hz heq
  apply H.symm.injective
  apply hUinj hy hz
  apply hamiltonZero_nonfolded_annulus_target_injective hwidth (h0 i) (h1 i) (hne i) (theta i)
  rw [← hformula, ← hformula, ← hH, ← hH, H.apply_symm_apply, H.apply_symm_apply]
  exact heq

end PoincareConjecture.M76
