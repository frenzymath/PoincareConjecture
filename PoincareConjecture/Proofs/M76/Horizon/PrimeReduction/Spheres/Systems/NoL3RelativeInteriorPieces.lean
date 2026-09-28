import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3RelativeCutBallObstruction
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalInteriorBallComponent

set_option autoImplicit false
open Set Geometry Metric
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem HasNoPuncturedSphereComponents.original_tetrahedral_piece_meets_boundary_relative
    {E E' X ι κ ν : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace X] [T2Space X] [Finite κ] [Finite ν]
    {e : ι → OpenPartialHomeomorph X V3} {Q F : Set X} {f : X → E'}
    (hno : HasNoPuncturedSphereComponents e f Q)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hS : ∀ i, S i ⊆ g '' K.space)
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hQ : IsCompact Q) (hQPL : PLDomain e Q)
    (B : ν → Set X) (sB : ∀ i, ChartwisePLSphere e (B i))
    (hBdis : Pairwise fun i j => Disjoint (B i) (B j))
    (hfront : frontier Q = F ∪ ⋃ i, B i)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hfi : InjOn f (g '' K.space)) (hSQ : Disjoint (⋃ i, S i) Q)
    {V : κ → Type*} [∀ i, TopologicalSpace (V i)]
    (A : ∀ i, Set (V i)) (HB : ∀ i, A i ≃ₜ S i)
    (c : ∀ i, V i × ℝ → X) (ε : κ → ℝ)
    (hε : ∀ i, 0 < ε i ∧ ε i ≤ 1)
    (hc : ∀ i, ContinuousOn (c i) (A i ×ˢ Icc (-1 : ℝ) 1))
    (hci : ∀ i, Topology.IsEmbedding
      (fun z : (A i ×ˢ Icc (-1 : ℝ) 1 : Set (V i × ℝ)) => c i z))
    (hc0 : ∀ i (z : A i), c i ((z : V i),0) = (HB i z : X))
    (hopen : ∀ i, IsOpen (c i '' (A i ×ˢ Ioo (-ε i) (ε i))))
    (hend : ∀ i (b : Bool),
      c i '' (A i ×ˢ ({if b then ε i else -ε i} : Set ℝ)) ⊆ Q)
    {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    (hTF : Disjoint (interior (g '' convexHull ℝ (t : Set E))) F)
    {x : X} (hx : x ∈ (g '' convexHull ℝ (t : Set E)) ∩ (⋃ i, S i)) :
    ¬ Disjoint
      (connectedComponentIn ((g '' convexHull ℝ (t : Set E)) ∩ (⋃ i, S i)) x)
      (g '' intrinsicFrontier ℝ (convexHull ℝ (t : Set E))) := by
  intro hmiss
  obtain ⟨i,D,hDt,⟨ball⟩,_⟩ := exists_original_interior_ball_component
    he K hK g hg hgi S sS hS hdis ht ht4 x hx hmiss
  have hDg : D ⊆ g '' K.space :=
    hDt.trans (interior_subset.trans (image_mono (K.convexHull_subset_space ht)))
  have hcenter : c i '' (A i ×ˢ ({0} : Set ℝ)) = S i := by
    ext y
    constructor
    · rintro ⟨⟨z,u⟩,⟨hz,hu⟩,rfl⟩
      have hu0 : u = 0 := hu
      subst u
      rw [hc0 i ⟨z,hz⟩]
      exact (HB i ⟨z,hz⟩).property
    · intro hy
      let z := (HB i).symm ⟨y,hy⟩
      refine ⟨((z : V i),0),⟨z.property,rfl⟩,?_⟩
      exact (hc0 i z).trans (congrArg Subtype.val ((HB i).apply_symm_apply ⟨y,hy⟩))
  have hSne : (S i).Nonempty := (isConnected_iff_connectedSpace.mpr
    ((sS i).parametrization.connectedSpace_iff.mp (isConnected_iff_connectedSpace.mp
      (isConnected_sphere (by simp) (0 : V3) zero_le_one)))).nonempty
  have hinj : InjOn (c i) (A i ×ˢ Icc (-1 : ℝ) 1) := by
    intro z hz w hw hzw
    exact congrArg Subtype.val ((hci i).injective (a₁ := ⟨z,hz⟩) (a₂ := ⟨w,hw⟩) hzw)
  exact hno.not_ball_with_retained_collar_relative_boundary ball hQ hQPL B sB hBdis
    hfront (hTF.mono (interior_subset.trans hDt) Subset.rfl) hf
    (hfi.mono hDg) (hSQ.mono (subset_iUnion S i) Subset.rfl)
    (hε i).1 (hε i).2 (hc i) hinj (hopen i) hcenter hSne (hend i)

end PoincareConjecture.M76
