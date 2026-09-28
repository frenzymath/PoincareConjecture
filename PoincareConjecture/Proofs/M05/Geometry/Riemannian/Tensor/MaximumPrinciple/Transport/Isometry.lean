import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.MaximumPrinciple.Transport.MetricCompatibility
import Mathlib.Analysis.InnerProductSpace.Orthonormal

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.LeviCivitaData

private theorem exists_linearIsometryEquiv_of_basis_pairings
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (w : ι → F)
    (hw : ∀ i j, inner ℝ (w i) (w j) = inner ℝ (b i) (b j))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    ∃ P : E ≃ₗᵢ[ℝ] F, ∀ v, P v = ∑ i, b.repr v i • w i := by
  classical
  let L : E →ₗ[ℝ] F := b.toBasis.constr ℝ w
  have hL : Orthonormal ℝ (L ∘ b.toBasis) := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [Function.comp_apply, L, Module.Basis.constr_basis]
    exact (hw i j).trans ((orthonormal_iff_ite.mp b.orthonormal) i j)
  let f := L.isometryOfOrthonormal b.orthonormal hL
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp f.injective
  refine ⟨LinearIsometryEquiv.ofSurjective f hsurj, ?_⟩
  intro v
  change b.toBasis.constr ℝ w v = _
  simp [Module.Basis.constr_apply_fintype]

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

def radialNeighborhood (p : M) (r : ℝ) : Set M :=
  (extChartAt (𝓡 n) p).source ∩
    {x | extChartAt (𝓡 n) p x - extChartAt (𝓡 n) p p ∈ Metric.ball 0 r}

omit [IsManifold (𝓡 n) ∞ M] in
lemma isOpen_radialNeighborhood (p : M) (r : ℝ) : IsOpen (radialNeighborhood (n := n) p r) := by
  have hc : ContinuousOn (fun x => extChartAt (𝓡 n) p x - extChartAt (𝓡 n) p p)
      (extChartAt (𝓡 n) p).source :=
    (continuousOn_extChartAt (I := 𝓡 n) p).sub continuousOn_const
  exact hc.isOpen_inter_preimage (isOpen_extChartAt_source p) Metric.isOpen_ball

omit [IsManifold (𝓡 n) ∞ M] in
lemma mem_radialNeighborhood (p : M) {r : ℝ} (hr : 0 < r) :
    p ∈ radialNeighborhood (n := n) p r := by
  exact ⟨mem_extChartAt_source p, by simpa only [mem_ofPred_eq, sub_self] using
    (Metric.mem_ball_self hr : (0 : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball 0 r)⟩

theorem exists_radialParallelIsometries_with_basis_jets (D : LeviCivitaData g) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ (r : ℝ)
      (Y : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) p)) →
        EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      0 < r ∧ Metric.ball 0 r ⊆ centeredChartDomain (n := n) p ∧
      (∀ i, ContDiff ℝ ∞ (Y i)) ∧
      (∀ i, fieldFromCenteredCoordinates p (Y i) p = g.orthonormalBasis p i) ∧
      (∀ i u, u ∈ Metric.ball 0 r → ∀ t ∈ Icc (-1 : ℝ) 1,
        HasDerivAt (fun s : ℝ => Y i (s • u))
          (-(D.centeredConnectionCoefficient p (t • u) u (Y i (t • u)))) t) ∧
      (∀ i a, D.connection (fieldFromCenteredCoordinates p (Y i)) p a = 0) ∧
      (∀ i a, D.connection (D.covariantDerivativeOnFields
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a)
        (fieldFromCenteredCoordinates p (Y i))) p a = 0) ∧
      ∃ P : (x : radialNeighborhood (n := n) p r) →
          TangentSpace (𝓡 n) p ≃ₗᵢ[ℝ] TangentSpace (𝓡 n) x.1,
        ∀ x v, P x v = ∑ i, (g.orthonormalBasis p).repr v i •
          fieldFromCenteredCoordinates p (Y i) x.1 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis p
  choose ρ Y hρ hρU hY hinit hpar hfirst hsecond using
    fun i => D.exists_radialParallelField p (b i)
  have hnhds : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℝ (Fin n)),
      z ∈ centeredChartDomain (n := n) p ∧ ∀ i, z ∈ Metric.ball 0 (ρ i) := by
    refine Filter.Eventually.and
      ((isOpen_centeredChartDomain p).mem_nhds (zero_mem_centeredChartDomain p)) ?_
    exact Filter.eventually_all.mpr fun i => Metric.ball_mem_nhds _ (hρ i)
  obtain ⟨r, hr, hrball⟩ := Metric.mem_nhds_iff.mp hnhds
  have hrU : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ centeredChartDomain p :=
    fun z hz => (hrball hz).1
  have hparallel i u (hu : u ∈ Metric.ball 0 r) t (ht : t ∈ Icc (-1 : ℝ) 1) :=
    hpar i u ((hrball hu).2 i) t ht
  have hP : ∀ x : radialNeighborhood (n := n) p r,
      ∃ P : TangentSpace (𝓡 n) p ≃ₗᵢ[ℝ] TangentSpace (𝓡 n) x.1,
        ∀ v, P v = ∑ i, b.repr v i • fieldFromCenteredCoordinates p (Y i) x.1 := by
    intro x
    let : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) := by
      unfold TangentSpace
      infer_instance
    let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x.1) := by
      unfold TangentSpace
      infer_instance
    apply exists_linearIsometryEquiv_of_basis_pairings b
      (fun i => fieldFromCenteredCoordinates p (Y i) x.1)
    · intro i j
      have h := D.inner_radialParallelFields p hrU (Y i) (Y j)
        (hparallel i) (hparallel j) x.2.1 x.2.2
      change g.inner x.1 (fieldFromCenteredCoordinates p (Y i) x.1)
        (fieldFromCenteredCoordinates p (Y j) x.1) = g.inner p (b i) (b j)
      simpa only [hinit] using h
    · unfold TangentSpace
      rfl
  choose P hP using hP
  exact ⟨r, Y, hr, hrU, hY, hinit, hparallel, hfirst, hsecond, P, hP⟩

theorem exists_radialParallelIsometries (D : LeviCivitaData g) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ (r : ℝ)
      (Y : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) p)) →
        EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      0 < r ∧ Metric.ball 0 r ⊆ centeredChartDomain (n := n) p ∧
      (∀ i, ContDiff ℝ ∞ (Y i)) ∧
      (∀ i, fieldFromCenteredCoordinates p (Y i) p = g.orthonormalBasis p i) ∧
      (∀ i u, u ∈ Metric.ball 0 r → ∀ t ∈ Icc (-1 : ℝ) 1,
        HasDerivAt (fun s : ℝ => Y i (s • u))
          (-(D.centeredConnectionCoefficient p (t • u) u (Y i (t • u)))) t) ∧
      ∃ P : (x : radialNeighborhood (n := n) p r) →
          TangentSpace (𝓡 n) p ≃ₗᵢ[ℝ] TangentSpace (𝓡 n) x.1,
        ∀ x v, P x v = ∑ i, (g.orthonormalBasis p).repr v i •
          fieldFromCenteredCoordinates p (Y i) x.1 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨r, Y, hr, hrU, hY, hinit, hpar, _, _, P, hP⟩ :=
    D.exists_radialParallelIsometries_with_basis_jets p
  exact ⟨r, Y, hr, hrU, hY, hinit, hpar, P, hP⟩

lemma fieldFromCenteredCoordinates_sum {ι : Type*} [Fintype ι] (p : M)
    (Y : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (a : ι → ℝ) (x : M) :
    fieldFromCenteredCoordinates p (fun z => ∑ i, a i • Y i z) x =
      ∑ i, a i • fieldFromCenteredCoordinates p (Y i) x := by
  unfold fieldFromCenteredCoordinates constantCoordinateField
  simp only [map_sum, map_smul]

private lemma connection_sum (D : LeviCivitaData g) {ι : Type*} (s : Finset ι)
    (W : ι → (x : M) → TangentSpace (𝓡 n) x) (p : M)
    (hW : ∀ i ∈ s, MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% (W i)) p) :
    D.connection (fun x => ∑ i ∈ s, W i x) p = ∑ i ∈ s, D.connection (W i) p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using! D.connection.isCovariantDerivativeOn.zero
  | @insert i s hi ih =>
    have hsum := MDifferentiableAt.sum_section (fun j hj => hW j (Finset.mem_insert_of_mem hj))
    simp only [Finset.sum_insert hi]
    change D.connection (W i + (fun x => ∑ j ∈ s, W j x)) p = _
    rw [D.connection.isCovariantDerivativeOn.add (hW i (Finset.mem_insert_self i s)) hsum]
    rw [ih (fun j hj => hW j (Finset.mem_insert_of_mem hj))]

private lemma connection_sum_smul (D : LeviCivitaData g) {ι : Type*} [Fintype ι]
    (W : ι → (x : M) → TangentSpace (𝓡 n) x) (a : ι → ℝ) (p : M)
    (hW : ∀ i, ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (W i)) p) :
    D.connection (fun x => ∑ i, a i • W i x) p = ∑ i, a i • D.connection (W i) p := by
  rw [connection_sum D Finset.univ (fun i x => a i • W i x) p
    (fun i _ => (hW i).const_smul_section.mdifferentiableAt (by simp))]
  apply Finset.sum_congr rfl
  intro i _
  exact D.connection.isCovariantDerivativeOn.smul_const (a i)
    ((hW i).mdifferentiableAt (by simp))

theorem exists_radialParallelIsometries_with_jets (D : LeviCivitaData g) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ (r : ℝ) (Y : TangentSpace (𝓡 n) p → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      0 < r ∧ Metric.ball 0 r ⊆ centeredChartDomain (n := n) p ∧
      (∀ v, ContDiff ℝ ∞ (Y v)) ∧
      (∀ v, fieldFromCenteredCoordinates p (Y v) p = v) ∧
      (∀ v u, u ∈ Metric.ball 0 r → ∀ t ∈ Icc (-1 : ℝ) 1,
        HasDerivAt (fun s : ℝ => Y v (s • u))
          (-(D.centeredConnectionCoefficient p (t • u) u (Y v (t • u)))) t) ∧
      (∀ v a, D.connection (fieldFromCenteredCoordinates p (Y v)) p a = 0) ∧
      (∀ v a, D.connection (D.covariantDerivativeOnFields
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a)
        (fieldFromCenteredCoordinates p (Y v))) p a = 0) ∧
      ∃ P : (x : radialNeighborhood (n := n) p r) →
          TangentSpace (𝓡 n) p ≃ₗᵢ[ℝ] TangentSpace (𝓡 n) x.1,
        ∀ x v, P x v = fieldFromCenteredCoordinates p (Y v) x.1 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨r, W, hr, hrU, hW, hinit, hparallel, hfirst, hsecond, P, hP⟩ :=
    D.exists_radialParallelIsometries_with_basis_jets p
  let b := g.orthonormalBasis p
  let Y : TangentSpace (𝓡 n) p → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun v z => ∑ i, b.repr v i • W i z
  have hY (v) : ContDiff ℝ ∞ (Y v) := by
    apply ContDiff.sum
    intro i _
    exact (hW i).const_smul (b.repr v i)
  have hsum (v) : fieldFromCenteredCoordinates p (Y v) =
      fun x => ∑ i, b.repr v i • fieldFromCenteredCoordinates p (W i) x :=
    funext (fieldFromCenteredCoordinates_sum p W (b.repr v))
  have hlift (i) (x) (hx : x ∈ (extChartAt (𝓡 n) p).source) :=
    contMDiffAt_fieldFromCenteredCoordinates p (hW i).contDiffAt hx
  refine ⟨r, Y, hr, hrU, hY, ?_, ?_, ?_, ?_, P, ?_⟩
  · intro v
    rw [fieldFromCenteredCoordinates_sum]
    simp only [hinit]
    exact b.sum_repr v
  · intro v u hu t ht
    have hd := HasDerivAt.sum (u := Finset.univ) fun i _ =>
      (hparallel i u hu t ht).const_smul (b.repr v i)
    convert! hd using 1
    · funext s
      simp only [Y, Finset.sum_apply, Pi.smul_apply]
    · simp only [Y, map_sum, map_smul, smul_neg, Finset.sum_neg_distrib]
  · intro v a
    rw [hsum, connection_sum_smul D _ _ p (fun i => hlift i p (mem_extChartAt_source p))]
    simp only [sum_apply, smul_apply, hfirst,
      smul_zero, Finset.sum_const_zero]
  · intro v a
    let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a
    let Z := fun i => D.covariantDerivativeOnFields X (fieldFromCenteredCoordinates p (W i))
    have hZ (i) := D.contMDiffAt_covariantDerivativeOnFields
      (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) a)
      (hlift i p (mem_extChartAt_source p))
    have hleft := D.contMDiffAt_covariantDerivativeOnFields
      (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) a)
      (contMDiffAt_fieldFromCenteredCoordinates p (hY v).contDiffAt (mem_extChartAt_source p))
    have heq : D.covariantDerivativeOnFields X (fieldFromCenteredCoordinates p (Y v)) =ᶠ[𝓝 p]
        fun x => ∑ i, b.repr v i • Z i x := by
      filter_upwards [extChartAt_source_mem_nhds (I := 𝓡 n) p] with x hx
      change D.connection (fieldFromCenteredCoordinates p (Y v)) x (X x) = _
      rw [hsum, connection_sum_smul D _ _ x (fun i => hlift i x hx)]
      simp only [sum_apply, smul_apply]
      rfl
    have hright := ContMDiffAt.sum_section (s := Finset.univ) fun i _ =>
      (hZ i).const_smul_section (a := b.repr v i)
    have hc := D.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (hleft.mdifferentiableAt (by simp)) (hright.mdifferentiableAt (by simp)) (by simp) heq
    change D.connection (D.covariantDerivativeOnFields X (fieldFromCenteredCoordinates p (Y v))) p a = 0
    rw [hc]
    change D.connection (fun x => ∑ i, b.repr v i • Z i x) p a = 0
    rw [connection_sum_smul D Z (b.repr v) p hZ]
    simp only [sum_apply, smul_apply]
    simp only [Z, X, hsecond, smul_zero, Finset.sum_const_zero]
  · intro x v
    rw [fieldFromCenteredCoordinates_sum]
    exact hP x v

theorem exists_radialParallelIsometries_with_fields (D : LeviCivitaData g) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ (r : ℝ) (Y : TangentSpace (𝓡 n) p → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      0 < r ∧ Metric.ball 0 r ⊆ centeredChartDomain (n := n) p ∧
      (∀ v, ContDiff ℝ ∞ (Y v)) ∧
      (∀ v, fieldFromCenteredCoordinates p (Y v) p = v) ∧
      (∀ v u, u ∈ Metric.ball 0 r → ∀ t ∈ Icc (-1 : ℝ) 1,
        HasDerivAt (fun s : ℝ => Y v (s • u))
          (-(D.centeredConnectionCoefficient p (t • u) u (Y v (t • u)))) t) ∧
      ∃ P : (x : radialNeighborhood (n := n) p r) →
          TangentSpace (𝓡 n) p ≃ₗᵢ[ℝ] TangentSpace (𝓡 n) x.1,
        ∀ x v, P x v = fieldFromCenteredCoordinates p (Y v) x.1 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨r, Y, hr, hrU, hY, hinit, hpar, _, _, P, hP⟩ :=
    D.exists_radialParallelIsometries_with_jets p
  exact ⟨r, Y, hr, hrU, hY, hinit, hpar, P, hP⟩

end PoincareConjecture.LeviCivitaData
