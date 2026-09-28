import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NormalFaceArcFamily
import PoincareConjecture.Proofs.M76.Mathlib.SimplexIntrinsicFrontier









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem original_edge_chart_mem_triangle_frontier
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (Q : OpenPartialHomeomorph X V3) (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    {a : Finset E} (has : a ⊆ s) (ha : a.card = 2)
    {x : X} (hx : x ∈ g '' convexHull ℝ (a : Set E)) :
    Q x ∈ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) := by
  classical
  have hAi : InjOn A (s : Set E) := by
    intro u hu v hv heq
    have hu' := subset_convexHull ℝ (s : Set E) hu
    have hv' := subset_convexHull ℝ (s : Set E) hv
    exact hgi (K.convexHull_subset_space hs hu') (K.convexHull_subset_space hs hv')
      (Q.injOn (hmap hu') (hmap hv') ((hA hu').trans (heq.trans (hA hv').symm)))
  have hind : AffineIndependent ℝ ((↑) : (s.image A) → V3) := by
    change AffineIndependent ℝ ((↑) : ↥((s.image A : Finset V3) : Set V3) → V3)
    rw [Finset.coe_image]
    exact affineIndependent_original_face_chart K g hgi hs Q A hmap hA
  obtain ⟨y, hy, rfl⟩ := hx
  have hys : y ∈ convexHull ℝ (s : Set E) := convexHull_mono has hy
  have hproper : a.image A ⊂ s.image A := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.image_subset_image has, ?_⟩
    intro heq
    have hc := congrArg Finset.card heq
    rw [Finset.card_image_of_injOn (hAi.mono has), Finset.card_image_of_injOn hAi,
      ha, hs3] at hc
    omega
  have hyA : A y ∈ convexHull ℝ ((a.image A : Finset V3) : Set V3) := by
    rw [Finset.coe_image]
    exact (A.toAffineMap.image_convexHull (a : Set E)).subset (mem_image_of_mem A hy)
  rw [show Q (g y) = A y from hA hys, ← Finset.coe_image]
  exact hind.convexHull_subset_intrinsicFrontier hproper hyA

theorem InCircleFreeNonreturningTriangleGraphPosition.exists_normal_arc_family_with_edge_contacts
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (Q : OpenPartialHomeomorph X V3) (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    {S : Set X} (hposition : InCircleFreeNonreturningTriangleGraphPosition Q S g s A) :
    ∃ (γ : Type) (_ : Finite γ) (d r : γ → Set V3),
      (Pairwise fun i j => Disjoint (d i) (d j)) ∧
      Q.symm '' (⋃ i, d i) = S ∩ (g '' convexHull ℝ (s : Set E)) ∧
      (⋃ i, d i) ⊆ convexHull ℝ (A '' (s : Set E)) ∩ Q.target ∧
      (∀ i, IsFinitePLBallPair ℝ (d i) (r i) ∧
        r i = d i ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))) ∧
      ∀ a : Finset E, a ⊆ s → a.card = 2 →
        ∀ x ∈ g '' convexHull ℝ (a : Set E),
          (x ∈ S ↔ ∃! i, Q x ∈ r i) := by
  classical
  obtain ⟨γ, hγ, d, r, hdis, hphysical, htarget, harcs⟩ :=
    hposition.exists_normal_arc_family K g hgi hs Q A hmap hA
  refine ⟨γ, hγ, d, r, hdis, hphysical, htarget,
    fun i => ⟨(harcs i).1, (harcs i).2.1⟩, ?_⟩
  intro a has ha x hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hys : y ∈ convexHull ℝ (s : Set E) := convexHull_mono has hy
  have hsource := hmap hys
  have hfront := original_edge_chart_mem_triangle_frontier K g hgi hs hs3 Q A hmap hA
    has ha (mem_image_of_mem g hy)
  constructor
  · intro hyS
    obtain ⟨z, hz, hzy⟩ := hphysical.symm.subset ⟨hyS, ⟨y, hys, rfl⟩⟩
    have hzT := (htarget hz).2
    have hQy : Q (g y) = z := hzy ▸ Q.right_inv hzT
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    have hiR : Q (g y) ∈ r i := (harcs i).2.1.symm ▸ ⟨hQy.symm ▸ hi, hfront⟩
    refine ⟨i, hiR, ?_⟩
    intro j hj
    by_contra hji
    exact Set.disjoint_left.mp (hdis hji) ((harcs j).1.1 hj) ((harcs i).1.1 hiR)
  · rintro ⟨i, hi, _⟩
    have hmem := hphysical.subset
      ⟨Q (g y), mem_iUnion.mpr ⟨i, (harcs i).1.1 hi⟩, Q.left_inv hsource⟩
    exact hmem.1

end PoincareConjecture.M76
