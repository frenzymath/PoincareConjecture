import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.ConvexFrontierSides
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.CoordinateTriangleEndpointCrossing
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.BoundaryDisks.SurfaceRimIncidence
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.SphereCutPLDomain
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SphereExteriorPosition
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalProtectedExteriorDomain









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

theorem compatible_paired_chart_of_coordinate_crossing
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S M : Set X}
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (C : OpenPartialHomeomorph V3 C3)
    (hC : LocallyPiecewiseAffineOn C C.source)
    {x : X} (hxQ : x ∈ Q.source) (hxC : Q x ∈ C.source) (hCx : C (Q x) = 0)
    (hS : ∀ z ∈ C.source, Q.symm z ∈ S ↔ (C z).2 = 0)
    (hM : ∀ z ∈ C.source, Q.symm z ∈ M ↔ (C z).1.1 = 0) :
    ∃ H : OpenPartialHomeomorph X V3,
      x ∈ H.source ∧ H x = 0 ∧
      (∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ H.source, y ∈ S ↔ H y 1 = 0) ∧
      ∀ y ∈ H.source, y ∈ M ↔ H y 0 = 0 := by
  let A := crossingCoordinateOrder.toHomeomorph.toOpenPartialHomeomorph
  let B := C.trans A
  have hB : B ∈ piecewiseAffineGroupoid V3 := by
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    exact (locallyPiecewiseAffineOn_affine
      crossingCoordinateOrder.toContinuousAffineMap isOpen_univ).comp hC
  let H := Q.trans B
  have hH (i : ι) : (e i).symm.trans H ∈ piecewiseAffineGroupoid V3 := by
    simpa only [H,OpenPartialHomeomorph.trans_assoc] using
      (piecewiseAffineGroupoid V3).trans (hQ i) hB
  refine ⟨H,⟨hxQ,hxC,mem_univ _⟩,?_,hH,?_,?_⟩
  · change crossingCoordinateOrder (C (Q x)) = 0
    rw [hCx]
    funext i
    fin_cases i <;> simp [crossingCoordinateOrder_apply]
  · intro y hy
    have hh := hS (Q y) hy.2.1
    change y ∈ S ↔ crossingCoordinateOrder (C (Q y)) 1 = 0
    rw [crossingCoordinateOrder_apply]
    simpa only [Matrix.cons_val_one,Matrix.cons_val_zero,Q.left_inv hy.1] using hh
  · intro y hy
    have hh := hM (Q y) hy.2.1
    change y ∈ M ↔ crossingCoordinateOrder (C (Q y)) 0 = 0
    rw [crossingCoordinateOrder_apply]
    simpa only [Matrix.cons_val_zero,Q.left_inv hy.1] using hh

theorem ChartwisePLSphere.surface_rim_charts_of_frontier_crossings
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {E S : Set X}
    (s : ChartwisePLSphere e S) (he : PLDomain e E)
    (hcross : ∀ x ∈ S ∩ frontier E, ∃ H : OpenPartialHomeomorph X V3,
      x ∈ H.source ∧ H x = 0 ∧
      (∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ H.source, y ∈ S ↔ H y 1 = 0) ∧
      ∀ y ∈ H.source, y ∈ frontier E ↔ H y 0 = 0) :
    ∀ x ∈ S ∩ E, ∃ T : OpenPartialHomeomorph X V3,
      x ∈ T.source ∧ (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      ((∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3), ell.contLinear v = 1 ∧
          (∀ y ∈ T.source, y ∈ S ∩ E ↔ ell (T y) = 0) ∧
          Disjoint T.source (S ∩ frontier E)) ∨
        ∃ (ell psi : V3 →ᴬ[ℝ] ℝ) (u v : V3),
          psi.contLinear u = 1 ∧ ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
          (∀ y ∈ T.source, y ∈ S ∩ E ↔ ell (T y) = 0 ∧ 0 ≤ psi (T y)) ∧
          ∀ y ∈ T.source, y ∈ S ∩ frontier E ↔ ell (T y) = 0 ∧ psi (T y) = 0) := by
  intro x hx
  by_cases hxf : x ∈ frontier E
  · obtain ⟨H,hxH,hHz,hHe,hHS,hHE⟩ := hcross x ⟨hx.1,hxf⟩
    obtain ⟨T,hxT,_,hcv,hTH,_,_,hval,_⟩ :=
      H.exists_convex_target_avoiding hxH hHz isClosed_empty (notMem_empty x)
    have hTe (i : ι) : (e i).symm.trans T ∈ piecewiseAffineGroupoid V3 := by
      apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
      have h := (hHe i).1.mono ((e i).symm.trans T).open_source
        (fun _ hz => ⟨hz.1,hTH hz.2⟩)
      exact h.congr (fun z _ => (hval ((e i).symm z)).symm)
    let ell : V3 →ᴬ[ℝ] ℝ := (ContinuousLinearMap.proj 1).toContinuousAffineMap
    let psi : V3 →L[ℝ] ℝ := ContinuousLinearMap.proj 0
    have hS (y : X) (hy : y ∈ T.source) : y ∈ S ↔ ell (T y) = 0 := by
      change y ∈ S ↔ T y 1 = 0
      rw [hval]
      exact hHS y (hTH hy)
    have hE (y : X) (hy : y ∈ T.source) : y ∈ frontier E ↔ psi (T y) = 0 := by
      change y ∈ frontier E ↔ T y 0 = 0
      rw [hval]
      exact hHE y (hTH hy)
    rcases halfspace_of_convex_linear_frontier_chart he.closed he.closure_interior
      hxf T hxT psi hcv hE with hpos | hneg
    · refine ⟨T,hxT,hTe,Or.inr ⟨ell,psi.toContinuousAffineMap,
        Pi.single 0 1,Pi.single 1 1,?_,?_,?_,?_,?_⟩⟩
      · simp [psi]
      · simp [ell]
      · simp [psi]
      · intro y hy
        exact and_congr (hS y hy) (hpos y hy)
      · intro y hy
        exact and_congr (hS y hy) (hE y hy)
    · refine ⟨T,hxT,hTe,Or.inr ⟨ell,-psi.toContinuousAffineMap,
        Pi.single 0 (-1),Pi.single 1 1,?_,?_,?_,?_,?_⟩⟩
      · simp [psi]
      · simp [ell]
      · simp [psi]
      · intro y hy
        change (y ∈ S ∧ y ∈ E) ↔ ell (T y) = 0 ∧ 0 ≤ -psi (T y)
        simpa only [neg_nonneg] using
          and_congr (hS y hy) (hneg y hy)
      · intro y hy
        change (y ∈ S ∧ y ∈ frontier E) ↔ ell (T y) = 0 ∧ -psi (T y) = 0
        simpa only [neg_eq_zero] using
          and_congr (hS y hy) (hE y hy)
  · have hxint : x ∈ interior E := (mem_interior_iff_notMem_frontier hx.2).mpr hxf
    obtain ⟨H,hxH,hHz,hHe,hHS⟩ := s.exists_pair_chart he.compatible
      (fun y _ => he.cover y) hx.1
    obtain ⟨T,hxT,_,_,hTH,_,hdis,hval,_⟩ :=
      H.exists_convex_target_avoiding hxH hHz (isOpen_interior (s := E)).isClosed_compl
        (by simpa only [mem_compl_iff,not_not] using hxint)
    have hTe (i : ι) : (e i).symm.trans T ∈ piecewiseAffineGroupoid V3 := by
      apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
      have h := (hHe i).1.mono ((e i).symm.trans T).open_source
        (fun _ hz => ⟨hz.1,hTH hz.2⟩)
      exact h.congr (fun z _ => (hval ((e i).symm z)).symm)
    have hTint (y : X) (hy : y ∈ T.source) : y ∈ interior E := by
      by_contra hn
      exact disjoint_left.mp hdis hy hn
    refine ⟨T,hxT,hTe,Or.inl ⟨(ContinuousLinearMap.proj 0).toContinuousAffineMap,
      Pi.single 0 1,by simp,?_,?_⟩⟩
    · intro y hy
      change (y ∈ S ∧ y ∈ E) ↔ T y 0 = 0
      rw [and_iff_left (interior_subset (hTint y hy)),hval]
      exact hHS y (hTH hy)
    · exact disjoint_left.mpr (fun y hy hm => hm.2.2 (hTint y hy))

theorem exists_signed_frontier_crossing_chart
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {E S : Set X}
    (he : PLDomain e E) {x : X} (hx : x ∈ frontier E)
    (H : OpenPartialHomeomorph X V3) (hxH : x ∈ H.source) (hHz : H x = 0)
    (hHe : ∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid V3)
    (hHS : ∀ y ∈ H.source, y ∈ S ↔ H y 1 = 0)
    (hHE : ∀ y ∈ H.source, y ∈ frontier E ↔ H y 0 = 0) :
    ∃ T : OpenPartialHomeomorph X V3,
      x ∈ T.source ∧ T x = 0 ∧
      (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ T.source, y ∈ S ↔ T y 1 = 0) ∧
      (∀ y ∈ T.source, y ∈ frontier E ↔ T y 0 = 0) ∧
      ((∀ y ∈ T.source, y ∈ E ↔ 0 ≤ T y 0) ∨
        (∀ y ∈ T.source, y ∈ E ↔ T y 0 ≤ 0)) := by
  obtain ⟨T,hxT,hTz,hcv,hTH,_,_,hval,_⟩ :=
    H.exists_convex_target_avoiding hxH hHz isClosed_empty (notMem_empty x)
  have hTe (i : ι) : (e i).symm.trans T ∈ piecewiseAffineGroupoid V3 := by
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    have h := (hHe i).1.mono ((e i).symm.trans T).open_source
      (fun _ hz => ⟨hz.1,hTH hz.2⟩)
    exact h.congr (fun z _ => (hval ((e i).symm z)).symm)
  have hfront (y : X) (hy : y ∈ T.source) : y ∈ frontier E ↔ T y 0 = 0 := by
    rw [hval]
    exact hHE y (hTH hy)
  refine ⟨T,hxT,hTz,hTe,?_,hfront,?_⟩
  · intro y hy
    rw [hval]
    exact hHS y (hTH hy)
  · exact halfspace_of_convex_linear_frontier_chart he.closed he.closure_interior
      hx T hxT (ContinuousLinearMap.proj 0) hcv hfront

theorem HamiltonMarkedProtectedBall.exists_positioned_exterior_surface_charts
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D S : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (s : ChartwisePLSphere e S) (hSR : S ⊆ interior (latticeHandleDomain ι κ L)) :
    let R := latticeHandleDomain ι κ L
    let E := closure (R \ D)
    ∃ Phi : LatticeHandleAmbient ι κ L ≃ₜ LatticeHandleAmbient ι κ L,
      EqOn Phi id (interior R)ᶜ ∧
      (∀ i j, (e i).symm.trans (Phi.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (Phi.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      Nonempty (ChartwisePLSphere e (Phi '' S)) ∧ Phi '' S ⊆ interior R ∧
      ∀ x ∈ Phi '' S ∩ frontier E,
        ∃ T : OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3,
          x ∈ T.source ∧ T x = 0 ∧
          (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
          (∀ y ∈ T.source, y ∈ Phi '' S ↔ T y 1 = 0) ∧
          (∀ y ∈ T.source, y ∈ frontier E ↔ T y 0 = 0) ∧
          ((∀ y ∈ T.source, y ∈ E ↔ 0 ≤ T y 0) ∨
            (∀ y ∈ T.source, y ∈ E ↔ T y 0 ≤ 0)) := by
  obtain ⟨Q,Phi,G,_,hQ,hfix,hPhi,hPhiinv,hs,hSR',hCQ,hG,hGs,hGc,hdeg,hcross⟩ :=
    b.exists_sphere_exterior_position he hdim hi s hSR
  refine ⟨Phi,hfix,hPhi,hPhiinv,hs,hSR',?_⟩
  intro x hx
  obtain ⟨C,hxC,_,_,hCz,hC,_,hCS,hCE⟩ :=
    hcross (Q x) (hGs.symm.subset ⟨x,hx,rfl⟩) univ isOpen_univ (mem_univ _)
  obtain ⟨H,hxH,hHz,hHe,hHS,hHE⟩ :=
    compatible_paired_chart_of_coordinate_crossing Q hQ C hC (hCQ hx) hxC hCz hCS hCE
  exact exists_signed_frontier_crossing_chart (b.plDomain_closed_complement he hdim hi)
    hx.2 H hxH hHz hHe hHS hHE

end PoincareConjecture.M76
