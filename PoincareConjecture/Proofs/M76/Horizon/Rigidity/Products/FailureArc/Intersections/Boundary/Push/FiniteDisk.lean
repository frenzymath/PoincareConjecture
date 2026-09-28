import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Push.RelativeDisk



set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "J" => Icc (0 : ℝ) 1

theorem exists_original_standard_proper_disk_parameter
    {X ι E : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    {d q : Set E} (hd : IsFinitePLBallPair P2 d q)
    {f : E → X} (hf : PolyhedralPLInCharts e f d) (hfi : InjOn f d)
    (hfR : MapsTo f d R) (hproper : ∀ x ∈ d, f x ∈ frontier R ↔ x ∈ q) :
    ∃ j : V2 → X, PolyhedralPLInCharts e j Disk ∧ InjOn j Disk ∧
      MapsTo j Disk R ∧ (∀ x ∈ Disk, j x ∈ frontier R ↔ x ∈ Rim) ∧
      j '' Disk = f '' d := by
  have hDisk : IsFinitePLBallPair P2 Disk Rim :=
    (isFinitePLBallPair_unit_cube (ι := Fin 2)).model_equiv
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  obtain ⟨H, hH, hHrim⟩ := hDisk.exists_homeomorph hd
  obtain ⟨u, hu, huval⟩ := hH
  have humap : MapsTo u Disk d := by
    intro x hx
    rw [← huval ⟨x, hx⟩]
    exact (H ⟨x, hx⟩).property
  have hui : InjOn u Disk := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((huval ⟨x, hx⟩).trans (hxy.trans (huval ⟨y, hy⟩).symm))))
  have hju : PolyhedralPLInCharts e (f ∘ u) Disk := by
    obtain ⟨K, hK, hKs, hKf⟩ := hu
    rw [← hKs]
    exact hf.comp_finitePiecewiseAffineOn K hK ⟨K, hK, rfl, hKf⟩
      (fun _ hx ↦ humap (hKs.subset hx))
  refine ⟨f ∘ u, hju, hfi.comp hui humap, fun x hx ↦ hfR (humap hx), ?_, ?_⟩
  · intro x hx
    rw [Function.comp_apply, hproper _ (humap hx), ← huval ⟨x, hx⟩]
    exact (hHrim ⟨x, hx⟩).symm
  · apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨u x, humap hx, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx⟩ := H.surjective ⟨y, hy⟩
      exact ⟨x, x.property, congrArg f ((huval x).symm.trans (congrArg Subtype.val hx))⟩

theorem exists_original_relative_finite_proper_disk_push
    {X ι E F B : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace B] [CompactSpace B] [PreconnectedSpace B]
    {e : ι → OpenPartialHomeomorph X V3} {R A T Z O : Set X}
    (hR : IsCompact R) (he : PLDomain e R)
    {D Q : Set F} (hD : IsFinitePLBallPair P2 D Q)
    {g : F → X} (hg : PolyhedralPLInCharts e g D) (hgi : InjOn g D)
    (hgR : MapsTo g D R) (hgproper : ∀ x ∈ D, g x ∈ frontier R ↔ x ∈ Q)
    (hO : IsOpen O) (hgO : g '' D ⊆ O)
    {d q W : Set E} {a b : E}
    (hd : IsFinitePLBallPair P2 d q) (hW : IsFinitePLBallPair ℝ W {a, b})
    (hWq : W ⊆ q) (hab : a ≠ b)
    {f : E → X} (hf : PolyhedralPLInCharts e f d) (hfi : InjOn f d)
    (hsubset : f '' d ⊆ g '' D)
    (hA : IsClosed A) (hT : IsClosed T) (hZ : IsClosed Z)
    (hWA : Disjoint (f '' W) A) (hfZ : Disjoint (f '' d) Z)
    (hfT : ∀ x ∈ d, f x ∈ T ↔ x ∈ W)
    (p : B × J → X) (hp : Continuous p) (hpR : ∀ z, p z ∈ R)
    (hp0 : ∀ b, p (b, ⟨0, by norm_num⟩) ∈ g '' D)
    (hpzero : ∀ z, p z ∈ g '' D ↔ (z.2 : ℝ) = 0)
    (hcover : A ⊆ (g '' D) ∪ range p ∪ Z) :
    ∃ k : E → X, PolyhedralPLInCharts e k d ∧ InjOn k d ∧
      MapsTo k d R ∧ MapsTo k d O ∧ EqOn k f W ∧
      Disjoint (k '' d) A ∧ (∀ x ∈ d, k x ∈ T ↔ x ∈ W) ∧
      ∀ x ∈ d, k x ∈ frontier R ↔ f x ∈ frontier R := by
  obtain ⟨j, hj, hji, hjR, hjproper, himage⟩ :=
    exists_original_standard_proper_disk_parameter hD hg hgi hgR hgproper
  apply exists_original_relative_proper_disk_push hR he hj hji hjR hjproper hO
    (himage.subset.trans hgO) hd hW hWq hab hf hfi (hsubset.trans himage.superset)
    hA hT hZ hWA hfZ hfT p hp hpR
  · exact fun b ↦ himage.superset (hp0 b)
  · exact fun z ↦ by rw [himage]; exact hpzero z
  · simpa only [himage] using hcover

end PoincareConjecture.M76.Dehn.Annuli
