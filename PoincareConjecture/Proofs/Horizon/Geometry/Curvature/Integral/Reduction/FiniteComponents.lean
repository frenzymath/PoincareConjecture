import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Reduction.Connected
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.LocalFinite

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory TopologicalSpace Function
open scoped Manifold ContDiff Bundle BigOperators
namespace PoincareConjecture.RiemannianMetric
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem integral_connectedComponentMetric
    (g : RiemannianMetric n M) (p : M) (f : M → ℝ) :
    (∫ x, f x ∂(g.connectedComponentMetric p).volumeMeasure) =
      ∫ x in connectedComponent p, f x ∂g.volumeMeasure := by
  let U := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
  have hi : MeasurableEmbedding (Subtype.val : U → M) :=
    MeasurableEmbedding.subtype_coe U.isOpen.measurableSet
  have hmap := map_volumeMeasure_subtype_val isClosed_connectedComponent g
    (g.connectedComponentMetric p) (fun _ _ _ => rfl)
  have he := hi.integral_map (μ := (g.connectedComponentMetric p).volumeMeasure) f
  rw [hmap] at he
  exact he.symm

theorem integral_eq_sum_connectedComponentMetric
    [Finite (ConnectedComponents M)]
    (g : RiemannianMetric n M) (f : M → ℝ) (hf : Integrable f g.volumeMeasure) :
    letI := Fintype.ofFinite (ConnectedComponents M)
    (∫ x, f x ∂g.volumeMeasure) =
      ∑ c : ConnectedComponents M,
        ∫ x, f x ∂(g.connectedComponentMetric (Quotient.out c)).volumeMeasure := by
  classical
  let := Fintype.ofFinite (ConnectedComponents M)
  have hmem (x:M) (c:ConnectedComponents M) :
      x∈connectedComponent (Quotient.out c) ↔ ConnectedComponents.mk x=c := by
    rw [←ConnectedComponents.coe_eq_coe']
    change ConnectedComponents.mk x=Quotient.mk'' (Quotient.out c) ↔ _
    rw [Quotient.out_eq']
  have hcover : (⋃ c:ConnectedComponents M, connectedComponent (Quotient.out c))=univ := by
    ext x
    simp only [mem_iUnion,mem_univ,iff_true]
    exact ⟨ConnectedComponents.mk x,(hmem x _).mpr rfl⟩
  have hdisj : Pairwise (Disjoint on (fun c:ConnectedComponents M =>
      connectedComponent (Quotient.out c))) := by
    intro c d hcd
    apply disjoint_left.mpr
    intro x hx hx'
    exact hcd (((hmem x c).mp hx).symm.trans ((hmem x d).mp hx'))
  have he := integral_iUnion_fintype
    (fun c:ConnectedComponents M => (isClosed_connectedComponent (x := Quotient.out c)).measurableSet)
    hdisj (fun _ => hf.integrableOn)
  rw [hcover,setIntegral_univ] at he
  simpa only [integral_connectedComponentMetric] using he

theorem integral_pos_scalarCurvature_eq_sum_connectedComponentMetric
    [CompactSpace M] (g : RiemannianMetric n M) (D : LeviCivitaData g) :
    letI : LocallyConnectedSpace M :=
      ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
    letI := Fintype.ofFinite (ConnectedComponents M)
    (∫ x, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) =
      ∑ c : ConnectedComponents M,
        ∫ x, max 0 ((g.connectedComponentMetric (Quotient.out c)).leviCivitaData.scalarCurvature x)
          ∂(g.connectedComponentMetric (Quotient.out c)).volumeMeasure := by
  classical
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  let := Fintype.ofFinite (ConnectedComponents M)
  have hf : Integrable (fun x => max 0 (D.scalarCurvature x)) g.volumeMeasure :=
    (continuous_const.max D.continuous_scalarCurvature).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_eq_sum_connectedComponentMetric g _ hf]
  apply Finset.sum_congr rfl
  intro c _
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  symm
  exact (g.connectedComponentMetric (Quotient.out c)).leviCivitaData.scalarCurvature_eq_of_local_isometry
    D isOpen_univ contMDiff_subtype_val.contMDiffOn (fun _ _ _ _ => rfl) (mem_univ x)

theorem integral_pos_scalarCurvature_le_of_connectedComponent_bounds
    [CompactSpace M] (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (E : M → ℝ) (hE : Integrable E g.volumeMeasure)
    {A C : ℝ} (hA : 0≤A) (hC : 0≤C) (N : ℕ)
    (hcount : Nat.card (ConnectedComponents M)≤N)
    (hbound : ∀ p:M,
      (∫ x, max 0 ((g.connectedComponentMetric p).leviCivitaData.scalarCurvature x)
        ∂(g.connectedComponentMetric p).volumeMeasure) ≤
      C*(A+∫ x, E x ∂(g.connectedComponentMetric p).volumeMeasure)) :
    (∫ x, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
      C*((N:ℝ)*A+∫ x, E x ∂g.volumeMeasure) := by
  classical
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  let := Fintype.ofFinite (ConnectedComponents M)
  rw [integral_pos_scalarCurvature_eq_sum_connectedComponentMetric g D]
  calc
    _ ≤ ∑ c:ConnectedComponents M,
        C*(A+∫ x, E x ∂(g.connectedComponentMetric (Quotient.out c)).volumeMeasure) :=
      Finset.sum_le_sum (fun c _ => hbound (Quotient.out c))
    _ = C*((Nat.card (ConnectedComponents M):ℝ)*A+∫ x, E x ∂g.volumeMeasure) := by
      rw [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,
        Finset.card_univ,nsmul_eq_mul,←Nat.card_eq_fintype_card,
        ←integral_eq_sum_connectedComponentMetric g E hE]
    _ ≤ _ := by
      gcongr

end PoincareConjecture.RiemannianMetric
