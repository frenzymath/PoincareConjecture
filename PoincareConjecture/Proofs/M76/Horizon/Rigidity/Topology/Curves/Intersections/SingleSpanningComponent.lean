import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Relation.Model
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalBoundary
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedInterval
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Intersections.ProperAnnularRims

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.SurfaceIntersectionComponents

variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Source : Set E} {Target : Set F} {f : E → X} {g : F → X} {rim : Set F}

theorem image_right_space_eq_intersection
    (C : SurfaceIntersectionComponents Source Target f g rim) :
    g '' C.right.space = f '' Source ∩ g '' Target := by
  rw [C.right_space]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy.2, y, hy.1, rfl⟩
  · rintro ⟨hx, y, hy, rfl⟩
    exact ⟨y, ⟨hy, hx⟩, rfl⟩

open Classical in

theorem exists_single_spanning_interval
    (C : SurfaceIntersectionComponents Source Target f g rim)
    (hgi : InjOn g Target) (mark : Set X) (p : X)
    (hsingle : (f '' Source ∩ g '' Target) ∩ mark = {p})
    (hreaches : ∀ i, ∃ y ∈ C.pieces i, g y ∈ mark)
    (hrim : ∀ y ∈ C.right.space, g y ∈ mark → y ∈ rim) :
    ∃ (i : C.right.vertexAbstractComplex.edgeGraph.ConnectedComponent) (y₀ y₁ : F),
      (∀ k, k = i) ∧ C.right.space = C.pieces i ∧
      IsFinitePLBallPair ℝ C.right.space (C.right.space ∩ rim) ∧
      y₀ ≠ y₁ ∧ C.right.space ∩ rim = {y₀, y₁} ∧
      g y₀ = p ∧ g y₁ ∉ mark ∧ (C.right.space ∩ rim).ncard = 2 ∧
      f '' Source ∩ g '' Target = g '' C.pieces i := by
  classical
  have hp : p ∈ (f '' Source ∩ g '' Target) ∩ mark :=
    hsingle.symm ▸ mem_singleton p
  obtain ⟨y₀, hyT, hgp⟩ := hp.1.2
  have hyS : y₀ ∈ C.right.space := C.right_space.symm.subset
    ⟨hyT, hgp.symm ▸ hp.1.1⟩
  obtain ⟨i, hyi⟩ := mem_iUnion.mp (C.cover.subset hyS)
  have hyMark : g y₀ ∈ mark := hgp.symm ▸ hp.2
  have hyRim : y₀ ∈ rim := hrim y₀ hyS hyMark
  have hpiece (k) : C.pieces k ⊆ C.right.space :=
    (subset_iUnion C.pieces k).trans C.cover.symm.subset
  have huniq (k) : k = i := by
    obtain ⟨z, hzk, hzMark⟩ := hreaches k
    have hzS := hpiece k hzk
    have hzData := C.right_space.subset hzS
    have hzp : g z = p := mem_singleton_iff.mp (hsingle.subset
      ⟨⟨hzData.2, z, hzData.1, rfl⟩, hzMark⟩)
    have hzy : z = y₀ := hgi hzData.1 hyT (hzp.trans hgp.symm)
    by_contra hki
    exact disjoint_left.mp (C.disjoint hki) (hzy ▸ hzk) hyi
  have hspace : C.right.space = C.pieces i := by
    rw [C.cover]
    apply Subset.antisymm
    · intro x hx
      obtain ⟨k, hk⟩ := mem_iUnion.mp hx
      exact huniq k ▸ hk
    · exact subset_iUnion C.pieces i
  have hball : IsFinitePLBallPair ℝ C.right.space (C.right.space ∩ rim) := by
    rcases C.models i with hball | ⟨n, P, _, _, _, hdisj⟩
    · exact hspace.symm ▸ hball
    · exact (disjoint_left.mp hdisj hyi hyRim).elim
  obtain ⟨a, b, hab, habound⟩ := hball.exists_boundary_eq_pair
  have hyPair : y₀ ∈ ({a, b} : Set F) := habound.subset ⟨hyS, hyRim⟩
  obtain ⟨y₁, hyne, hboundary⟩ : ∃ y₁ : F, y₀ ≠ y₁ ∧
      C.right.space ∩ rim = {y₀, y₁} := by
    rcases hyPair with rfl | rfl
    · exact ⟨b, hab, habound⟩
    · exact ⟨a, hab.symm, habound.trans (pair_comm a y₀)⟩
  have hy₁S : y₁ ∈ C.right.space :=
    (hboundary.symm.subset (mem_insert_of_mem y₀ (mem_singleton y₁))).1
  have hy₁Mark : g y₁ ∉ mark := by
    intro hm
    have hy₁Data := C.right_space.subset hy₁S
    have hgp₁ : g y₁ = p := mem_singleton_iff.mp (hsingle.subset
      ⟨⟨hy₁Data.2, y₁, hy₁Data.1, rfl⟩, hm⟩)
    exact hyne (hgi hyT hy₁Data.1 (hgp.trans hgp₁.symm))
  refine ⟨i, y₀, y₁, huniq, hspace, hball, hyne, hboundary, hgp,
    hy₁Mark, hball.ncard_boundary_eq_two, ?_⟩
  rw [← C.image_right_space_eq_intersection, hspace]

theorem component_card_eq_one_of_single_mark
    (C : SurfaceIntersectionComponents Source Target f g rim)
    (hgi : InjOn g Target) (mark : Set X) (p : X)
    (hsingle : (f '' Source ∩ g '' Target) ∩ mark = {p})
    (hreaches : ∀ i, ∃ y ∈ C.pieces i, g y ∈ mark)
    (hrim : ∀ y ∈ C.right.space, g y ∈ mark → y ∈ rim) :
    Nat.card (ConnectedComponents C.right.space) = 1 := by
  obtain ⟨i, _, _, huniq, _⟩ :=
    C.exists_single_spanning_interval hgi mark p hsingle hreaches hrim
  rw [Nat.card_congr C.intrinsic]
  exact Nat.card_eq_one_iff_exists.mpr ⟨i, huniq⟩

theorem exists_marked_spanning_interval_parametrization [FiniteDimensional ℝ F]
    (C : SurfaceIntersectionComponents Source Target f g rim)
    (hgi : InjOn g Target) (mark : Set X) (p : X)
    (hsingle : (f '' Source ∩ g '' Target) ∩ mark = {p})
    (hreaches : ∀ i, ∃ y ∈ C.pieces i, g y ∈ mark)
    (hrim : ∀ y ∈ C.right.space, g y ∈ mark → y ∈ rim) :
    ∃ H : unitInterval ≃ₜ C.right.space,
      H.IsFinitePL ∧ H.symm.IsFinitePL ∧ g (H 0) = p ∧ g (H 1) ∉ mark ∧
      (∀ t : unitInterval, (H t : F) ∈ rim ↔ t = 0 ∨ t = 1) ∧
      (∀ t : unitInterval, g (H t) ∈ mark ↔ t = 0) := by
  obtain ⟨_, a, b, _, _, hball, hab, hboundary, hga, hgb, _⟩ :=
    C.exists_single_spanning_interval hgi mark p hsingle hreaches hrim
  have hpair : IsFinitePLBallPair ℝ C.right.space {a, b} := hboundary ▸ hball
  obtain ⟨H, hH, h0, h1⟩ := hpair.exists_unitInterval_chart_with_endpoints hab
  have hzero (t : unitInterval) : (H t : F) = a ↔ t = 0 := by
    rw [← h0]
    exact ⟨fun h => H.injective (Subtype.ext h), fun h => h ▸ rfl⟩
  have hone (t : unitInterval) : (H t : F) = b ↔ t = 1 := by
    rw [← h1]
    exact ⟨fun h => H.injective (Subtype.ext h), fun h => h ▸ rfl⟩
  refine ⟨H, hH, hH.symm, ?_, ?_, ?_, ?_⟩
  · change g (H ⟨0, _⟩ : F) = p
    rw [h0, hga]
  · change g (H ⟨1, _⟩ : F) ∉ mark
    rw [h1]
    exact hgb
  · intro t
    have hm : (H t : F) ∈ rim ↔ (H t : F) ∈ C.right.space ∩ rim :=
      ⟨fun h => ⟨(H t).property, h⟩, fun h => h.2⟩
    rw [hm, hboundary]
    exact (or_congr (hzero t) (hone t))
  · intro t
    constructor
    · intro ht
      have htData := C.right_space.subset (H t).property
      have hgp : g (H t) = p := mem_singleton_iff.mp (hsingle.subset
        ⟨⟨htData.2, H t, htData.1, rfl⟩, ht⟩)
      have haData := C.right_space.subset (H 0).property
      apply (hzero t).mp
      have ht0 : (H t : F) = H 0 := hgi htData.1 haData.1
        ((hgp.trans hga.symm).trans (congrArg g h0.symm))
      exact ht0.trans h0
    · rintro rfl
      change g (H ⟨0, _⟩ : F) ∈ mark
      rw [h0, hga]
      exact (hsingle.symm.subset (mem_singleton p)).2

end PoincareConjecture.M76.SurfaceIntersectionComponents

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

open Metric
local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "Rim" => Set.prod (sphere (0 : V1) 1) (sphere (0 : V2) 1)

theorem exists_proper_annular_spanning_interval
    {X : Type*} [TopologicalSpace X] {R S₀ S₁ : Set X}
    (hS₀ : S₀ ⊆ frontier R) (g : Bool → (V1 × V2) → X)
    (C : SurfaceIntersectionComponents source source (g false) (g true) Rim)
    (hgi : InjOn (g true) source)
    (hproper : ∀ x : source,
      g true x ∈ frontier R ↔ (x : V1 × V2).1 ∈ sphere (0 : V1) 1)
    (hfalse : ∀ z : Q2, g true (endpoint false, z) ∈ S₀)
    (htrue : ∀ z : Q2, g true (endpoint true, z) ∈ S₁)
    (p : X) (hsingle : (g false '' source ∩ g true '' source) ∩ S₀ = {p})
    (hreaches : ∀ i, ∃ y ∈ C.pieces i, g true y ∈ S₀) :
    ∃ H : unitInterval ≃ₜ C.right.space,
      H.IsFinitePL ∧ H.symm.IsFinitePL ∧
      g true (H 0) = p ∧ g true (H 1) ∈ S₁ ∧
      (∀ t : unitInterval, g true (H t) ∈ frontier R ↔ t = 0 ∨ t = 1) ∧
      (∀ t : unitInterval, g true (H t) ∈ S₀ ↔ t = 0) ∧
      Nat.card (ConnectedComponents C.right.space) = 1 := by
  have hrim (y : V1 × V2) (hy : y ∈ C.right.space) (hm : g true y ∈ S₀) : y ∈ Rim := by
    have hySource := (C.right_space.subset hy).1
    exact ⟨(hproper ⟨y, hySource⟩).mp (hS₀ hm), hySource.2⟩
  obtain ⟨H, hH, hHi, h0, h1, hboundary, hmark⟩ :=
    C.exists_marked_spanning_interval_parametrization hgi S₀ p hsingle hreaches hrim
  have hsource (t : unitInterval) : (H t : V1 × V2) ∈ source :=
    (C.right_space.subset (H t).property).1
  have hother : g true (H 1) ∈ S₁ := by
    have hRim := (hboundary 1).mpr (Or.inr rfl)
    obtain ⟨b, hb⟩ := (mem_sphere_iff_exists_endpoint (H 1 : V1 × V2).1).mp hRim.1
    have hpair : (H 1 : V1 × V2) = (endpoint b, (H 1 : V1 × V2).2) := Prod.ext hb rfl
    cases b
    · exact (h1 (by rw [hpair]; exact hfalse ⟨_, (hsource 1).2⟩)).elim
    · rw [hpair]
      exact htrue ⟨_, (hsource 1).2⟩
  refine ⟨H, hH, hHi, h0, hother, ?_, hmark,
    C.component_card_eq_one_of_single_mark hgi S₀ p hsingle hreaches hrim⟩
  intro t
  rw [hproper ⟨H t, hsource t⟩, ← hboundary t]
  exact ⟨fun hx => ⟨hx, (hsource t).2⟩, fun hx => hx.1⟩

theorem exists_coordinate_annuli_spanning_interval
    {Circle X : Type*} [TopologicalSpace Circle] [TopologicalSpace X]
    {R S₀ S₁ : Set X} (hS₀ : S₀ ⊆ frontier R) (hdis : Disjoint S₀ S₁)
    (h : (Circle × Circle) ≃ₜ S₀) (q : Bool → Q2 ≃ₜ Circle) (a : Circle)
    (g : Bool → (V1 × V2) → X)
    (C : SurfaceIntersectionComponents source source (g false) (g true) Rim)
    (hgi : InjOn (g true) source)
    (hproper : ∀ b, ∀ x : source,
      g b x ∈ frontier R ↔ (x : V1 × V2).1 ∈ sphere (0 : V1) 1)
    (hfalse : ∀ z : Q2, g false (endpoint false, z) = (h (q false z, a) : X))
    (htrue : ∀ z : Q2, g true (endpoint false, z) = (h (a, q true z) : X))
    (hother : ∀ b (z : Q2), g b (endpoint true, z) ∈ S₁)
    (hreaches : ∀ i, ∃ y ∈ C.pieces i, g true y ∈ S₀) :
    ∃ H : unitInterval ≃ₜ C.right.space,
      H.IsFinitePL ∧ H.symm.IsFinitePL ∧
      g true (H 0) = (h (a, a) : X) ∧ g true (H 1) ∈ S₁ ∧
      (∀ t : unitInterval, g true (H t) ∈ frontier R ↔ t = 0 ∨ t = 1) ∧
      (∀ t : unitInterval, g true (H t) ∈ S₀ ↔ t = 0) ∧
      Nat.card (ConnectedComponents C.right.space) = 1 := by
  exact exists_proper_annular_spanning_interval hS₀ g C hgi (hproper true)
    (fun z => by rw [htrue]; exact (h _).property) (hother true) (h (a, a))
    (coordinate_proper_annuli_intersection_on_mark hS₀ hdis h q a g hproper hfalse htrue hother)
    hreaches

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
