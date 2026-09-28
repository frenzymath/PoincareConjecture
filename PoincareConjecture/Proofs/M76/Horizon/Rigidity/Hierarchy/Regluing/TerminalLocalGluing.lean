import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Maps.SourceBoundaryAlternative
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.RectangleFaces
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.ClosedSeamLocalInjectivity
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.FirstRectangleFaces

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

private theorem exists_open_injOn_closed_piece
    {X Y : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A)
    {f : X → Y} (hf : IsLocallyInjective (fun x : A => f x)) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ InjOn f (U ∩ A) := by
  exact _root_.Dehn.exists_open_injOn_inter_closed hA hf x

theorem isLocallyInjective_of_saturated_closed_attachment
    {X Y : Type*} [TopologicalSpace X] {S B C : Set X}
    (hB : IsClosed B) (hC : IsClosed C) (hcover : S ⊆ B ∪ C)
    {f : X → Y}
    (hfB : IsLocallyInjective (fun x : B => f x))
    (hfC : IsLocallyInjective (fun x : C => f x))
    (hsat : ∀ x ∈ S, ∀ y ∈ S, x ∈ C → f x = f y → y ∈ C) :
    IsLocallyInjective (fun x : S => f x) := by
  intro x
  obtain ⟨U, hU, hxU, hiU⟩ := exists_open_injOn_closed_piece hB hfB (x : X)
  obtain ⟨V, hV, hxV, hiV⟩ := exists_open_injOn_closed_piece hC hfC (x : X)
  refine ⟨Subtype.val ⁻¹' (U ∩ V),
    (hU.inter hV).preimage continuous_subtype_val, ⟨hxU, hxV⟩, ?_⟩
  intro y hy z hz heq
  apply Subtype.ext
  by_cases hyC : (y : X) ∈ C
  · exact hiV ⟨hy.2, hyC⟩ ⟨hz.2, hsat y y.property z z.property hyC heq⟩ heq
  by_cases hzC : (z : X) ∈ C
  · exact False.elim (hyC (hsat z z.property y y.property hzC heq.symm))
  exact hiU ⟨hy.1, (hcover y.property).resolve_right hyC⟩
    ⟨hz.1, (hcover z.property).resolve_right hzC⟩ heq

theorem isLocallyInjective_on_finite_disjoint_closed_faces
    {X Y η : Type*} [TopologicalSpace X] [Finite η]
    (M : η → Set X) (hM : ∀ i, IsClosed (M i))
    (hdis : Pairwise (fun i k => Disjoint (M i) (M k)))
    {f : X → Y} (hf : ∀ i, IsLocallyInjective (fun x : M i => f x)) :
    IsLocallyInjective (fun x : (⋃ i, M i) => f x) := by
  classical
  intro x
  obtain ⟨i, hxi⟩ := mem_iUnion.mp x.property
  obtain ⟨U, hU, hxU, hiU⟩ := exists_open_injOn_closed_piece (hM i) (hf i) (x : X)
  let bad : Set X := ⋃ k : {k : η // k ≠ i}, M k
  have hbad : IsClosed bad := isClosed_iUnion_of_finite (fun k => hM k)
  have hxnot : (x : X) ∉ bad := by
    intro hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    exact disjoint_left.mp (hdis k.property) hk hxi
  have hsub (y : (⋃ i, M i)) (hy : (y : X) ∉ bad) : (y : X) ∈ M i := by
    obtain ⟨k, hk⟩ := mem_iUnion.mp y.property
    by_cases hki : k = i
    · exact hki ▸ hk
    · exact False.elim (hy (mem_iUnion.mpr ⟨⟨k, hki⟩, hk⟩))
  refine ⟨Subtype.val ⁻¹' (U ∩ badᶜ),
    (hU.inter hbad.isOpen_compl).preimage continuous_subtype_val, ⟨hxU, hxnot⟩, ?_⟩
  intro y hy z hz heq
  exact Subtype.ext (hiU ⟨hy.1, hsub y hy.2⟩ ⟨hz.1, hsub z hz.2⟩ heq)

theorem isLocallyInjective_of_finite_saturated_closed_faces
    {X Y η : Type*} [TopologicalSpace X] [Finite η]
    {S B : Set X} (hB : IsClosed B) (M : η → Set X)
    (hM : ∀ i, IsClosed (M i))
    (hdis : Pairwise (fun i k => Disjoint (M i) (M k)))
    (hcover : S ⊆ B ∪ ⋃ i, M i) {f : X → Y}
    (hfB : IsLocallyInjective (fun x : B => f x))
    (hf : ∀ i, IsLocallyInjective (fun x : M i => f x))
    (hsat : ∀ x ∈ S, ∀ y ∈ S, x ∈ ⋃ i, M i → f x = f y → y ∈ ⋃ i, M i) :
    IsLocallyInjective (fun x : S => f x) :=
  isLocallyInjective_of_saturated_closed_attachment hB
    (isClosed_iUnion_of_finite hM) hcover hfB
    (isLocallyInjective_on_finite_disjoint_closed_faces M hM hdis hf) hsat

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Disk" => Metric.closedBall (0 : V2) 1
local notation "Ann" => PLAnnularStrip.squareAnnulus 8 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem hamiltonZero_installed_frontier_locally_injective
    {E : Type*} [TopologicalSpace E] {K : Set E} (hK : IsCompact K)
    {R : Set X0} {r : ℝ} (hr : 0 ≤ r) (c : E × ℝ → X0)
    (hc : ContinuousOn c (K ×ˢ Icc (-r) r))
    (hi : Topology.IsEmbedding (fun z : (K ×ˢ Icc (-r) r : Set (E × ℝ)) => c z))
    (hzero : c '' (K ×ˢ ({0} : Set ℝ)) = frontier R)
    (phi psi : C(H0, H0))
    (F : (hamiltonZeroAmbientMap phi).HomotopyRel
      (hamiltonZeroAmbientMap psi) (interior R)ᶜ)
    (g : C(K, C0 × C0)) (hg : IsCoveringMap g)
    (hproduct : ∀ x : K, (Q0 (hamiltonZeroAmbientMap phi (c (x, 0)))).1 = g x) :
    IsLocallyInjective (fun x : frontier R => hamiltonZeroAmbientMap psi x) := by
  obtain ⟨G, hG, hGval⟩ := exists_hamiltonZero_installed_frontier_tangential_covering
    hK hr c hc hi hzero phi psi F g hg hproduct
  intro x
  obtain ⟨U, hU, hx, hinj⟩ := hG.isLocalHomeomorph.isLocallyInjective x
  refine ⟨U, hU, hx, fun y hy z hz heq => hinj hy hz ?_⟩
  rw [hGval, hGval]
  exact congrArg (fun z : X0 => (Q0 z).1) heq

private theorem terminal_faces_locally_injective
    {N S : Set X0} {phi psi : C(H0, H0)} {u v : ℝ}
    (hthird : hamiltonZeroThirdCircleMap psi = hamiltonZeroThirdCircleMap phi)
    {n : Bool → ℕ} (j q : (Σ s : Bool, Fin (n s)) → V2 → X0)
    (hfamily : ∀ s : Bool, (⋃ i : Fin (n s), j ⟨s, i⟩ '' Disk) =
      N ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {((if s then v else u : ℝ) : C0)})
    (hclosed : ∀ i, IsClosed (j i '' Disk))
    (hdis : Pairwise (fun i k => Disjoint (j i '' Disk) (j k '' Disk)))
    (hq : ∀ i, InjOn (q i) Disk)
    (hvalue : ∀ i (z : Disk), hamiltonZeroAmbientMap psi (j i z) = q i z)
    (hold : IsLocallyInjective (fun x : frontier N => hamiltonZeroAmbientMap psi x))
    (hSN : S ⊆ N) (hcover : S ⊆ frontier N ∪ ⋃ i, j i '' Disk) :
    IsLocallyInjective (fun x : S => hamiltonZeroAmbientMap psi x) := by
  have hwhole : (⋃ i : Σ s : Bool, Fin (n s), j i '' Disk) =
      (N ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {(u : C0)}) ∪
        (N ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {(v : C0)}) := by
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
  apply isLocallyInjective_of_finite_saturated_closed_faces isClosed_frontier
    (fun i => j i '' Disk) hclosed hdis hcover hold
  · intro i
    apply Function.Injective.IsLocallyInjective
    rintro ⟨x, z, hz, rfl⟩ ⟨y, w, hw, rfl⟩ heq
    exact Subtype.ext (congrArg (j i) (hq i hz hw
      ((hvalue i ⟨z, hz⟩).symm.trans (heq.trans (hvalue i ⟨w, hw⟩)))))
  · intro x hx y hy hxphase heq
    have hqeq : hamiltonZeroThirdCircleMap phi x = hamiltonZeroThirdCircleMap phi y := by
      rw [← hthird, hamiltonZeroThirdCircleMap_ambient,
        hamiltonZeroThirdCircleMap_ambient, heq]
    rw [hwhole] at hxphase ⊢
    rcases hxphase with hxphase | hxphase
    · exact Or.inl ⟨hSN hy, hqeq.symm.trans hxphase.2⟩
    · exact Or.inr ⟨hSN hy, hqeq.symm.trans hxphase.2⟩

theorem hamiltonZero_terminal_frontier_union_locally_injective
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {N : Set X0} {phi psi : C(H0, H0)} {u v : ℝ}
    (terminal : HamiltonZeroTerminalThirdPhaseData e N phi u v)
    (hthird : hamiltonZeroThirdCircleMap psi = hamiltonZeroThirdCircleMap phi)
    {n : Bool → ℕ} (j q : (Σ s : Bool, Fin (n s)) → V2 → X0)
    (hfamily : ∀ s : Bool, (⋃ i : Fin (n s), j ⟨s, i⟩ '' Disk) =
      N ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {((if s then v else u : ℝ) : C0)})
    (hclosed : ∀ i, IsClosed (j i '' Disk))
    (hdis : Pairwise (fun i k => Disjoint (j i '' Disk) (j k '' Disk)))
    (hq : ∀ i, InjOn (q i) Disk)
    (hvalue : ∀ i (z : Disk), hamiltonZeroAmbientMap psi (j i z) = q i z)
    (hold : IsLocallyInjective (fun x : frontier N => hamiltonZeroAmbientMap psi x)) :
    let T := fun side : Bool => N ∩ hamiltonZeroThirdCircleMap psi ⁻¹'
      AddCircle.closedIntervalArc p (if side then v else u) (if side then u + p else v)
    IsLocallyInjective (fun x : (⋃ side, frontier (T side)) => hamiltonZeroAmbientMap psi x) := by
  intro T
  apply terminal_faces_locally_injective hthird j q hfamily hclosed hdis hq hvalue hold
  · apply iUnion_subset
    intro side x hx
    have hclosedT : IsClosed (T side) := by
      dsimp [T]
      rw [hthird]
      exact (terminal.geometry.slabs side).1.closed
    exact (hclosedT.frontier_subset hx).1
  · apply iUnion_subset
    intro side x hx
    change x ∈ frontier (N ∩ hamiltonZeroThirdCircleMap psi ⁻¹' _) at hx
    rw [hthird, (terminal.geometry.slabs side).2.1] at hx
    rcases hx with hx | hx | hx
    · exact Or.inl hx.2
    · obtain ⟨i, hi⟩ := mem_iUnion.mp ((hfamily false).symm.subset hx)
      exact Or.inr (mem_iUnion.mpr ⟨⟨false, i⟩, hi⟩)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp ((hfamily true).symm.subset hx)
      exact Or.inr (mem_iUnion.mpr ⟨⟨true, i⟩, hi⟩)

theorem hamiltonZero_terminal_frontier_locally_injective
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {N : Set X0} {phi psi : C(H0, H0)} {u v : ℝ}
    (terminal : HamiltonZeroTerminalThirdPhaseData e N phi u v)
    (hthird : hamiltonZeroThirdCircleMap psi = hamiltonZeroThirdCircleMap phi)
    {n : Bool → ℕ} (j q : (Σ s : Bool, Fin (n s)) → V2 → X0)
    (hfamily : ∀ s : Bool, (⋃ i : Fin (n s), j ⟨s, i⟩ '' Disk) =
      N ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {((if s then v else u : ℝ) : C0)})
    (hclosed : ∀ i, IsClosed (j i '' Disk))
    (hdis : Pairwise (fun i k => Disjoint (j i '' Disk) (j k '' Disk)))
    (hq : ∀ i, InjOn (q i) Disk)
    (hvalue : ∀ i (z : Disk), hamiltonZeroAmbientMap psi (j i z) = q i z)
    (hold : IsLocallyInjective (fun x : frontier N => hamiltonZeroAmbientMap psi x))
    (side : Bool) :
    let T := N ∩ hamiltonZeroThirdCircleMap psi ⁻¹'
      AddCircle.closedIntervalArc p (if side then v else u) (if side then u + p else v)
    IsLocallyInjective (fun x : frontier T => hamiltonZeroAmbientMap psi x) := by
  have h := hamiltonZero_terminal_frontier_union_locally_injective terminal hthird j q
    hfamily hclosed hdis hq hvalue hold
  exact h.comp_right (continuous_inclusion (subset_iUnion _ side)) (Set.inclusion_injective _)

private theorem locallyInjective_on_embedded_image
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} (j : X → Y) (hj : Topology.IsEmbedding (fun x : A => j x))
    (f : Y → Z) (hf : IsLocallyInjective (fun x : A => f (j x))) :
    IsLocallyInjective (fun x : j '' A => f x) := by
  rintro ⟨_, x, hx, rfl⟩
  obtain ⟨U, hU, hxU, hiU⟩ := hf ⟨x, hx⟩
  obtain ⟨V, hV, hVU⟩ := hj.isInducing.isOpen_iff.mp hU
  refine ⟨Subtype.val ⁻¹' V, hV.preimage continuous_subtype_val, ?_, ?_⟩
  · exact show (⟨x, hx⟩ : A) ∈ (fun x : A => j x) ⁻¹' V from hVU.symm ▸ hxU
  · rintro ⟨_, y, hy, rfl⟩ hyV ⟨_, z, hz, rfl⟩ hzV heq
    apply Subtype.ext
    exact congrArg (fun x : A => j x) (hiU
      (hVU ▸ (show (⟨y, hy⟩ : A) ∈ (fun x : A => j x) ⁻¹' V from hyV))
      (hVU ▸ (show (⟨z, hz⟩ : A) ∈ (fun x : A => j x) ⁻¹' V from hzV)) heq)

private theorem annulusTarget_injective
    {alpha beta delta0 delta1 : ℝ} (hwidth : beta < alpha + p)
    (h0 : delta0 ∈ Icc alpha beta) (h1 : delta1 ∈ Icc alpha beta)
    (hne : delta0 ≠ delta1) (theta : C0) :
    Function.Injective (hamiltonZeroAnnulusTargetMap delta0 delta1 theta) := by
  exact hamiltonZeroAnnulusTargetMap_injective hwidth h0 h1 hne theta

theorem hamiltonZero_nonfolded_annulus_locally_injective
    (phi : C(H0, H0)) (j : ℝ × ℝ → X0)
    (hj : Topology.IsEmbedding (fun z : Ann => j z))
    {alpha beta delta0 delta1 : ℝ} (hwidth : beta < alpha + p)
    (h0 : delta0 ∈ Icc alpha beta) (h1 : delta1 ∈ Icc alpha beta)
    (hne : delta0 ≠ delta1) (theta : C0)
    (c : C(Ann, unitInterval × C0)) (hc : IsCoveringMap c)
    (hformula : ∀ z : Ann, hamiltonZeroAmbientMap phi (j z) =
      hamiltonZeroAnnulusTargetMap delta0 delta1 theta (c z)) :
    IsLocallyInjective (fun x : j '' Ann => hamiltonZeroAmbientMap phi x) := by
  apply locallyInjective_on_embedded_image j hj
  have h := hc.isLocalHomeomorph.isLocallyInjective.comp_left
    (annulusTarget_injective hwidth h0 h1 hne theta)
  convert h using 1
  exact funext hformula

theorem hamiltonZero_second_slab_frontier_locally_injective
    {ι η : Type*} [Finite η] {e : ι → OpenPartialHomeomorph X0 V3}
    {R : Set X0} {phi : C(H0, H0)} {a b : ℝ}
    (geometry : HamiltonZeroSecondPhaseGeometry e R phi a b)
    (j : η → ℝ × ℝ → X0)
    (hclosed : ∀ i, IsClosed (j i '' Ann))
    (hdis : Pairwise (fun i k => Disjoint (j i '' Ann) (j k '' Ann)))
    (hwhole : (⋃ i, j i '' Ann) =
      (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(a : C0)}) ∪
        (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(b : C0)}))
    (hold : IsLocallyInjective (fun x : frontier R => hamiltonZeroAmbientMap phi x))
    (hface : ∀ i, IsLocallyInjective (fun x : j i '' Ann => hamiltonZeroAmbientMap phi x))
    (side : Bool) :
    let N := R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
      AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
    IsLocallyInjective (fun x : frontier N => hamiltonZeroAmbientMap phi x) := by
  intro N
  have hfront : frontier N = (N ∩ frontier R) ∪ ⋃ i, j i '' Ann := by
    rw [hwhole]
    exact (geometry.slabs side).2.1
  apply isLocallyInjective_of_finite_saturated_closed_faces isClosed_frontier
    (fun i => j i '' Ann) hclosed hdis
    (by rw [hfront]; exact union_subset_union inter_subset_right subset_rfl) hold hface
  intro x hx y hy hxphase heq
  have hyR : y ∈ R := ((geometry.slabs side).1.closed.frontier_subset hy).1
  have hqeq : hamiltonZeroSecondCircleMap phi x = hamiltonZeroSecondCircleMap phi y := by
    rw [hamiltonZeroSecondCircleMap_ambient, hamiltonZeroSecondCircleMap_ambient, heq]
  rw [hwhole] at hxphase ⊢
  rcases hxphase with hxphase | hxphase
  · exact Or.inl ⟨hyR, hqeq.symm.trans hxphase.2⟩
  · exact Or.inr ⟨hyR, hqeq.symm.trans hxphase.2⟩

theorem HamiltonZeroTerminalHomeomorphicDisks.exists_locally_injective_endpoint
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    {N : Set X0} {phi : C(H0, H0)} {u v alpha beta a b : ℝ}
    (good : HamiltonZeroTerminalHomeomorphicDisks e d N phi u v alpha beta a b)
    (terminal : HamiltonZeroTerminalThirdPhaseData e N phi u v)
    (hold : IsLocallyInjective (fun x : frontier N => hamiltonZeroAmbientMap phi x)) :
    ∃ psi : C(H0, H0),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧ Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      hamiltonZeroThirdCircleMap psi = hamiltonZeroThirdCircleMap phi ∧
      N ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta ∧
      N ⊆ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b ∧
      Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel
        (hamiltonZeroAmbientMap psi) (interior N)ᶜ) ∧
      IsLocallyInjective (fun x : (⋃ side : Bool, frontier
        (N ∩ hamiltonZeroThirdCircleMap psi ⁻¹'
          AddCircle.closedIntervalArc p (if side then v else u) (if side then u + p else v))) =>
        hamiltonZeroAmbientMap psi x) ∧
      ∀ side : Bool,
        let T := N ∩ hamiltonZeroThirdCircleMap psi ⁻¹'
          AddCircle.closedIntervalArc p (if side then v else u) (if side then u + p else v)
        IsLocallyInjective (fun x : frontier T => hamiltonZeroAmbientMap psi x) := by
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  obtain ⟨n, j, hfamily, hdis, hprops, installed⟩ := good
  obtain ⟨_, _, q, _, psi, _, _, _, _, _, _, _, hq, _, hpsi, Hpsi, Fpsi,
    hthird, hvalue, hfirst, hsecond, G, _, _⟩ := installed
  have holdPsi : IsLocallyInjective (fun x : frontier N => hamiltonZeroAmbientMap psi x) := by
    have heq : (fun x : frontier N => hamiltonZeroAmbientMap psi x) =
        (fun x : frontier N => hamiltonZeroAmbientMap phi x) :=
      funext (fun x => (G.fst_eq_snd x.property.2).symm)
    rw [heq]
    exact hold
  refine ⟨psi, hpsi, Hpsi, Fpsi, hthird, hfirst, hsecond, ⟨G⟩, ?_, ?_⟩
  · exact hamiltonZero_terminal_frontier_union_locally_injective terminal hthird j q hfamily
      (fun i => (hprops i).2.2.2.2.1.isClosed) hdis hq hvalue holdPsi
  · exact hamiltonZero_terminal_frontier_locally_injective terminal hthird j q hfamily
      (fun i => (hprops i).2.2.2.2.1.isClosed) hdis hq hvalue holdPsi

theorem HamiltonZeroSourceBoundaryDiskData.exists_locally_injective_terminal_endpoints
    {ι κ E : Type*} [TopologicalSpace E]
    {e : ι → OpenPartialHomeomorph X0 V3} {d : κ → OpenPartialHomeomorph X0 V3}
    {phi : C(H0, H0)} {R : Set X0} {alpha beta : ℝ}
    (data : HamiltonZeroSourceBoundaryDiskData e d phi R alpha beta)
    (hab : alpha < beta) (hwidth : beta < alpha + p)
    {K : Set E} (hK : IsCompact K) {r : ℝ} (hr : 0 ≤ r) (c0 : E × ℝ → X0)
    (hc0 : ContinuousOn c0 (K ×ˢ Icc (-r) r))
    (hi0 : Topology.IsEmbedding (fun z : (K ×ˢ Icc (-r) r : Set (E × ℝ)) => c0 z))
    (hzero : c0 '' (K ×ˢ ({0} : Set ℝ)) = frontier R)
    (g : C(K, C0 × C0)) (hg : IsCoveringMap g)
    (hproduct : ∀ x : K, (Q0 (hamiltonZeroAmbientMap phi (c0 (x, 0)))).1 = g x) :
    ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
      ∃ (chi eta : C(H0, H0)),
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 chi) ∧
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 eta) ∧
        Nonempty (phi.HomotopyRel eta B0) ∧
        Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel
          (hamiltonZeroAmbientMap eta) (interior R)ᶜ) ∧
        R ⊆ hamiltonZeroCircleMap eta ⁻¹' AddCircle.closedIntervalArc p alpha beta ∧
        R ⊆ hamiltonZeroCircleMap chi ⁻¹' AddCircle.closedIntervalArc p alpha beta ∧
        frontier R ⊆ hamiltonZeroCircleMap chi ⁻¹' {(alpha : C0), (beta : C0)} ∧
        HamiltonZeroSecondPhaseGeometry e R chi a b ∧
        ∀ s : Bool,
          let N := R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
            AddCircle.closedIntervalArc p (if s then b else a) (if s then a + p else b)
          ∃ u ∈ Ioo (p / 4) (p / 3), ∃ v ∈ Ioo (2 * p / 3) (3 * p / 4),
            HamiltonZeroTerminalThirdPhaseData e N eta u v ∧
            (∀ thirdSide : Bool,
              let T := N ∩ hamiltonZeroThirdCircleMap eta ⁻¹'
                AddCircle.closedIntervalArc p (if thirdSide then v else u)
                  (if thirdSide then u + p else v)
              ∀ x : T, Subsingleton (FundamentalGroup T x)) ∧
            ∃ psi : C(H0, H0),
              ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
              Nonempty (phi.HomotopyRel psi B0) ∧
              Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
              hamiltonZeroThirdCircleMap psi = hamiltonZeroThirdCircleMap eta ∧
              N ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta ∧
              N ⊆ hamiltonZeroSecondCircleMap psi ⁻¹'
                AddCircle.closedIntervalArc p (if s then b else a) (if s then a + p else b) ∧
              Nonempty ((hamiltonZeroAmbientMap eta).HomotopyRel
                (hamiltonZeroAmbientMap psi) (interior N)ᶜ) ∧
              EqOn (hamiltonZeroAmbientMap psi) (hamiltonZeroAmbientMap chi) (frontier N) ∧
              IsLocallyInjective (fun x : (⋃ side : Bool, frontier
                (N ∩ hamiltonZeroThirdCircleMap psi ⁻¹'
                  AddCircle.closedIntervalArc p (if side then v else u) (if side then u + p else v))) =>
                hamiltonZeroAmbientMap psi x) ∧
              ∀ side : Bool,
                let T := N ∩ hamiltonZeroThirdCircleMap psi ⁻¹'
                  AddCircle.closedIntervalArc p (if side then v else u) (if side then u + p else v)
                IsLocallyInjective (fun x : frontier T => hamiltonZeroAmbientMap psi x) := by
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let : CompactSpace Ann := Dehn.annulusCylinderHomeomorph.compactSpace
  obtain ⟨a, ha, b, hb, _, chi, eta, _, n, j, delta0, delta1, c, hchi, _, _, ⟨Gchi⟩,
    heta, _, ⟨Heta⟩, _, ⟨Geta⟩, _, _, _, hfirstEq, _, hRfirst, hRfront, geometry, _, _, _, hfamily, hdis,
    hprops, hfrontEq, terminal⟩ := data
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
  have hlabel0 (i) : delta0 i ∈ Icc alpha beta := by
    rcases (hprops i).2.2.2.1 with h | h
    · rw [h]; exact ⟨le_rfl, hab.le⟩
    · rw [show delta0 i = beta from h]; exact ⟨hab.le, le_rfl⟩
  have hlabel1 (i) : delta1 i ∈ Icc alpha beta := by
    rcases (hprops i).2.2.2.2.1 with h | h
    · rw [h]; exact ⟨le_rfl, hab.le⟩
    · rw [show delta1 i = beta from h]; exact ⟨hab.le, le_rfl⟩
  have hclosed (i) : IsClosed (j i '' Ann) := by
    have h := (isCompact_range (hprops i).2.1.continuous).isClosed
    have hrange : range (fun z : Ann => j i z) = j i '' Ann := by
      ext x
      simp
    rwa [hrange] at h
  have hold := hamiltonZero_installed_frontier_locally_injective hK hr c0 hc0 hi0
    hzero phi chi Gchi g hg hproduct
  have hface (i) : IsLocallyInjective (fun x : j i '' Ann => hamiltonZeroAmbientMap chi x) :=
    hamiltonZero_nonfolded_annulus_locally_injective chi (j i) (hprops i).2.1 hwidth
      (hlabel0 i) (hlabel1 i) (hprops i).2.2.2.2.2.1
      ((if i.1 then b else a : ℝ) : C0) (c i) (hprops i).2.2.2.2.2.2.1
      (hprops i).2.2.2.2.2.2.2.1
  refine ⟨a, ha, b, hb, chi, eta, hchi, heta, ⟨Heta⟩, ⟨Gchi.trans Geta⟩,
    hfirstEq.symm ▸ hRfirst, hRfirst, hRfront, geometry, ?_⟩
  intro s
  have hlocal := hamiltonZero_second_slab_frontier_locally_injective geometry j
    hclosed hdis hwhole hold hface s
  have hlocalEta : IsLocallyInjective (fun x : frontier
      (R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
        AddCircle.closedIntervalArc p (if s then b else a) (if s then a + p else b)) =>
      hamiltonZeroAmbientMap eta x) := by
    convert hlocal using 1
    exact funext (fun x => hfrontEq s x.property)
  obtain ⟨u, hu, v, hv, _, hterminal, _, hgroups, good⟩ := terminal s
  obtain ⟨psi, hpsi, ⟨Hpsi⟩, Fpsi, hthird, hfirst, hsecond, ⟨Gpsi⟩, hunion, hfull⟩ :=
    good.exists_locally_injective_endpoint hterminal hlocalEta
  refine ⟨u, hu, v, hv, hterminal, hgroups, psi, hpsi, ⟨Heta.trans Hpsi⟩, Fpsi,
    hthird, hfirst, hsecond, ⟨Gpsi⟩, ?_, hunion, hfull⟩
  exact fun _ hx => (Gpsi.fst_eq_snd hx.2).symm.trans (hfrontEq s hx)

end PoincareConjecture.M76
