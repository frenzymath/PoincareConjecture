import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.SphereBicollarLevelCharts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.ConvexFrontierSides
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.CollarCutCarrier
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.RegularClosedSphereCut
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.Topology
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ConvexTargetRestriction
import PoincareConjecture.Proofs.M76.Wall.ProtectedPLIntersection
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonWallComplementBall










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3}



theorem ChartwisePLSphere.exists_regular_boundary_halfspace_chart
    {S D A : Set X} (s : ChartwisePLSphere e S)
    (hD : IsClosed D) (hreg : closure (interior D) = D)
    (hA : IsClosed A)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (hfront : frontier D = A ∪ S) {x : X} (hx : x ∈ S) (hxA : x ∉ A) :
    ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3) (B : OpenPartialHomeomorph X V3),
      ell.contLinear v = 1 ∧ x ∈ B.source ∧ ell (B x) = 0 ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      ∀ y ∈ B.source, y ∈ D ↔ 0 ≤ ell (B y) := by
  obtain ⟨H, hxH, hHx, hHe, hHs⟩ :=
    s.exists_pair_chart hcompat (fun y _ => hcover y) hx
  obtain ⟨B, hxB, hBx, hcv, hBs, _, hBA, hval, _⟩ :=
    H.exists_convex_target_avoiding hxH hHx hA hxA
  have hBe (i : ι) : (e i).symm.trans B ∈ piecewiseAffineGroupoid V3 := by
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    have h := (hHe i).1.mono ((e i).symm.trans B).open_source
      (fun _ hz => ⟨hz.1, hBs hz.2⟩)
    apply h.congr
    intro z _
    exact (hval ((e i).symm z)).symm
  let ell : V3 →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have hBfront (y : X) (hy : y ∈ B.source) : y ∈ frontier D ↔ ell (B y) = 0 := by
    rw [hfront, mem_union, or_iff_right (fun ha => disjoint_left.mp hBA hy ha), hval]
    exact hHs y (hBs hy)
  have hxD : x ∈ frontier D := hfront.symm.subset (Or.inr hx)
  rcases halfspace_of_convex_linear_frontier_chart hD hreg hxD B hxB ell hcv hBfront
    with hpos | hneg
  · refine ⟨ell.toContinuousAffineMap, Pi.single 0 1, B, ?_, hxB, ?_, hBe, hpos⟩
    · simp [ell]
    · rw [hBx]
      rfl
  · refine ⟨-ell.toContinuousAffineMap, Pi.single 0 (-1), B, ?_, hxB, ?_, hBe, ?_⟩
    · simp [ell]
    · rw [hBx]
      simp
    · intro y hy
      simpa using hneg y hy





theorem PLDomain.sdiff_open_of_two_sphere_frontiers
    {R U Sm Sp : Set X} (he : PLDomain e R)
    (hR : IsCompact R) (hU : IsOpen U) (hUR : closure U ⊆ interior R)
    (sm : ChartwisePLSphere e Sm) (sp : ChartwisePLSphere e Sp)
    (hdis : Disjoint Sm Sp) (hfront : frontier U = Sm ∪ Sp)
    (hreg : closure (interior (R \ U)) = R \ U) :
    PLDomain e (R \ U) := by
  obtain ⟨hK, _, hKfront, _, _, holdnew⟩ := compact_collar_cut_geometry hR hU hUR
  rw [hfront] at hKfront holdnew
  refine ⟨he.cover, he.compatible, hK.isClosed, ?_⟩
  intro x hx
  by_cases hxC : x ∈ closure U
  · have hxnew : x ∈ Sm ∪ Sp := by
      rcases hKfront.subset hx with hold | hnew
      · exact False.elim (hold.2 (hUR hxC))
      · exact hnew
    rcases hxnew with hxm | hxp
    · apply sm.exists_regular_boundary_halfspace_chart (A := frontier R ∪ Sp) hK.isClosed hreg
        (isClosed_frontier.union sp.isCompact.isClosed) he.compatible he.cover
        (by rw [hKfront]; ext y; simp only [mem_union]; tauto) hxm
      rintro (hold | hxp)
      · exact disjoint_left.mp holdnew hold (Or.inl hxm)
      · exact disjoint_left.mp hdis hxm hxp
    · apply sp.exists_regular_boundary_halfspace_chart (A := frontier R ∪ Sm) hK.isClosed hreg
        (isClosed_frontier.union sm.isCompact.isClosed) he.compatible he.cover
        (by rw [hKfront, union_assoc]) hxp
      rintro (hold | hxm)
      · exact disjoint_left.mp holdnew hold (Or.inr hxp)
      · exact disjoint_left.mp hdis hxm hxp
  · have hxR : x ∈ frontier R := by
      rcases hKfront.subset hx with hold | hnew
      · exact hold
      · exact False.elim (hxC (frontier_subset_closure (hfront.symm.subset hnew)))
    obtain ⟨ell, v, H, hv, hxH, hzero, hcompat, hhalf⟩ := he.halfspace x hxR
    let B := H.restrOpen (closure U)ᶜ isClosed_closure.isOpen_compl
    refine ⟨ell, v, B, hv, ⟨hxH, hxC⟩, hzero, ?_, ?_⟩
    · intro i
      exact (e i).piecewiseAffine_compatible_restrOpen_right H (hcompat i)
        isClosed_closure.isOpen_compl
    · intro y hy
      change y ∈ R \ U ↔ 0 ≤ ell (H y)
      constructor
      · intro h
        exact (hhalf y hy.1).mp h.1
      · intro h
        exact ⟨(hhalf y hy.1).mpr h, fun hu => hy.2 (subset_closure hu)⟩





theorem ChartwisePLSphere.plDomain_bicollar_cut
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {R S : Set X} (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (F : X → E)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hFi : InjOn F S) {N : Set E} (hN : N = F '' S) (hNc : IsCompact N)
    (c : E × ℝ → X)
    (hc : PolyhedralPLInCharts e c (N ×ˢ Icc (-1 : ℝ) 1))
    (hci : Topology.IsEmbedding
      (fun z : (N ×ˢ Icc (-1 : ℝ) 1 : Set (E × ℝ)) => c z))
    {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε < δ) (hδ : δ ≤ 1)
    (hinside : MapsTo c (N ×ˢ Icc (-δ) δ) (interior R))
    (hopen : IsOpen (c '' (N ×ˢ Ioo (-ε) ε))) :
    PLDomain e (R \ c '' (N ×ˢ Ioo (-ε) ε)) := by
  have hεone : ε ≤ 1 := hεδ.le.trans hδ
  have hm : -ε ∈ Icc (-1 : ℝ) 1 := by constructor <;> linarith
  have hp : ε ∈ Icc (-1 : ℝ) 1 := by constructor <;> linarith
  obtain ⟨sm, _⟩ := s.exists_bicollar_level_sphere F hF hFi hN c hc hci hm
  obtain ⟨sp, _⟩ := s.exists_bicollar_level_sphere F hF hFi hN c hc hci hp
  have hcl := hc.continuousOn.closure_image_collar_strip hNc hε hεone
  have hclR : closure (c '' (N ×ˢ Ioo (-ε) ε)) ⊆ interior R := by
    rw [hcl]
    rintro _ ⟨z, hz, rfl⟩
    exact hinside ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  exact he.sdiff_open_of_two_sphere_frontiers hR hopen hclR sm sp
    (disjoint_collar_level_images c hci hm hp (by linarith))
    (hci.frontier_image_collar_strip hNc hε hεone hopen)
    (closure_interior_sphere_collar_cut hNc hR he.closure_interior hci
      hε hεδ hδ hinside hopen)

end PoincareConjecture.M76
