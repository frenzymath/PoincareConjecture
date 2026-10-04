import PoincareLib.Geometry.Riemannian.Homothety.Curvature.Bianchi

/-! Adapted from Mapher06/Poincare-MorganTian, `PoincareMT/Proofs/M13/CurvatureExtensions.lean`,
revision `0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. See `references/ricci-flow/mapher/rescaling-import.json`. -/

/-!
# Independence from the fixed local curvature extensions

Tensoriality gives pointwise dependence in the first two slots. The first
Bianchi identity transfers this dependence to the third slot.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.Homothety

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Three fixed extensions are smooth on a common open neighborhood. -/
theorem exists_open_smooth_extensions (x : M) (u v w : TangentSpace (𝓡 n) x) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (T% (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u)) U ∧
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (T% (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v)) U ∧
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (T% (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w)) U := by
  obtain ⟨s, hs, hsu⟩ := FiberBundle.exists_contMDiffOn_extend
    (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) u
  obtain ⟨t, ht, htv⟩ := FiberBundle.exists_contMDiffOn_extend
    (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) v
  obtain ⟨r, hr, hrw⟩ := FiberBundle.exists_contMDiffOn_extend
    (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) w
  refine ⟨interior (s ∩ t ∩ r), isOpen_interior,
    mem_interior_iff_mem_nhds.mpr (Filter.inter_mem (Filter.inter_mem hs ht) hr),
    hsu.mono (fun _ hp ↦ (interior_subset hp).1.1),
    htv.mono (fun _ hp ↦ (interior_subset hp).1.2),
    hrw.mono (fun _ hp ↦ (interior_subset hp).2)⟩

variable [T2Space M]

/-- The third field can be replaced by any smooth field with the same point value. -/
theorem curvatureOnFields_pointwise_third (D : LeviCivitaData g) (U : Set M) (hU : IsOpen U)
    (X Y Z Z' : (p : M) → TangentSpace (𝓡 n) p)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    (hZ' : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z') U)
    (x : M) (hx : x ∈ U) (hZZ' : Z x = Z' x) :
    D.curvatureOnFields X Y Z x = D.curvatureOnFields X Y Z' x := by
  have hZx := (hZ.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hZ'x := (hZ'.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hDX := ((connection_contMDiffOn g D U hU X hX).contMDiffAt
    (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hDY := ((connection_contMDiffOn g D U hU Y hY).contMDiffAt
    (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have h1 := (curvatureOnFields_tensorial_second D Y X x hDX).pointwise hZx hZ'x hZZ'
  have h2 := (curvatureOnFields_tensorial_first D X Y x hDY).pointwise hZx hZ'x hZZ'
  have hB := curvatureOnFields_bianchi D U hU X Y Z hX hY hZ x hx
  have hB' := curvatureOnFields_bianchi D U hU X Y Z' hX hY hZ' x hx
  rw [h1, h2] at hB
  exact add_right_cancel (add_right_cancel (hB.trans hB'.symm))

/-- The regular commutator depends only on the three point values. -/
theorem curvatureOnFields_pointwise (D : LeviCivitaData g) (U : Set M) (hU : IsOpen U)
    (X Y Z X' Y' Z' : (p : M) → TangentSpace (𝓡 n) p)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    (hX' : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X') U)
    (hY' : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y') U)
    (hZ' : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z') U)
    (x : M) (hx : x ∈ U) (hXX' : X x = X' x) (hYY' : Y x = Y' x) (hZZ' : Z x = Z' x) :
    D.curvatureOnFields X Y Z x = D.curvatureOnFields X' Y' Z' x := by
  have hDZ := ((connection_contMDiffOn g D U hU Z hZ).contMDiffAt
    (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  calc
    D.curvatureOnFields X Y Z x = D.curvatureOnFields X' Y Z x :=
      (curvatureOnFields_tensorial_first D Y Z x hDZ).pointwise
        ((hX.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
        ((hX'.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)) hXX'
    _ = D.curvatureOnFields X' Y' Z x :=
      (curvatureOnFields_tensorial_second D X' Z x hDZ).pointwise
        ((hY.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
        ((hY'.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)) hYY'
    _ = D.curvatureOnFields X' Y' Z' x :=
      curvatureOnFields_pointwise_third D U hU X' Y' Z Z' hX' hY' hZ hZ' x hx hZZ'

/-- Evaluate the fixed-extension curvature using arbitrary local smooth fields. -/
theorem curvature_eq_curvatureOnFields (D : LeviCivitaData g) (U : Set M) (hU : IsOpen U)
    (X Y Z : (p : M) → TangentSpace (𝓡 n) p)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    (x : M) (hx : x ∈ U) :
    D.curvature x (X x) (Y x) (Z x) = D.curvatureOnFields X Y Z x := by
  obtain ⟨V, hV, hxV, hEX, hEY, hEZ⟩ := exists_open_smooth_extensions x (X x) (Y x) (Z x)
  apply curvatureOnFields_pointwise D (U ∩ V) (hU.inter hV) _ _ _ X Y Z
    (hEX.mono Set.inter_subset_right) (hEY.mono Set.inter_subset_right)
    (hEZ.mono Set.inter_subset_right) (hX.mono Set.inter_subset_left)
    (hY.mono Set.inter_subset_left) (hZ.mono Set.inter_subset_left) x ⟨hx, hxV⟩ <;> simp

end PoincareMT.Homothety
