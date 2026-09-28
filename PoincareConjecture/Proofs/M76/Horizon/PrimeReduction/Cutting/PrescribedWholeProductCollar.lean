import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalOppositeProductCollar








set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

theorem ChartwisePLSphere.exists_original_opposite_unit_product_collar
    {X ι T : Type*} [MetricSpace X]
    [TopologicalSpace T] [CompactSpace T] [PreconnectedSpace T]
    {e : ι → OpenPartialHomeomorph X V3} {R S U : Set X}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (hSR : S ⊆ interior R) (hU : IsOpen U) (hSU : S ⊆ U)
    (j : V2 × T → X) (hj : Continuous (fun z : Disk × T => j (z.1,z.2)))
    (hproper : ∀ z ∈ Disk, ∀ t : T, j (z,t) ∈ S ↔ z ∈ Rim) :
    ∃ (t : Finset R) (N : SimplicialComplex ℝ (t → ℝ × V3))
      (C : (t → ℝ × V3) × ℝ → X) (K B : Set X),
      N.faces.Finite ∧ PolyhedralPLInCharts e C (N.space ×ˢ I) ∧
      InjOn C (N.space ×ˢ I) ∧
      K = C '' (N.space ×ˢ J) ∧
      S = C '' (N.space ×ˢ ({1 / 2} : Set ℝ)) ∧
      B = C '' (N.space ×ˢ ({-(1 / 2)} : Set ℝ)) ∧
      IsCompact K ∧ PLDomain e K ∧ K ⊆ U ∩ interior R ∧
      Nonempty (ChartwisePLSphere e B) ∧ Disjoint B S ∧
      frontier K = B ∪ S ∧ K ∩ (j '' (Disk ×ˢ (univ : Set T))) = j '' (Rim ×ˢ (univ : Set T)) ∧
      ∃ (c : (t → ℝ × V3) × ℝ → X) (ε : ℝ) (positive : Bool),
        PolyhedralPLInCharts e c (N.space ×ˢ I) ∧ InjOn c (N.space ×ˢ I) ∧
        0 < ε ∧ ε ≤ 1 / 4 ∧ IsConnected N.space ∧
        S = c '' (N.space ×ˢ ({0} : Set ℝ)) ∧
        MapsTo c (N.space ×ˢ Icc (-ε) ε) (U ∩ interior R) ∧
        IsOpen (c '' (N.space ×ˢ Ioo (-ε) ε)) ∧
        K = c '' (N.space ×ˢ (if positive then Icc (-ε) 0 else Icc 0 ε)) ∧
        interior K = c '' (N.space ×ˢ (if positive then Ioo (-ε) 0 else Ioo 0 ε)) ∧
        ∃ F : X → (t → ℝ × V3),
          (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
          InjOn F S ∧ N.space = F '' S := by
  let E₂ := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
  have hnorm (z : P2) : ‖E₂.symm z‖ = ‖z‖ := by
    change ‖![z.1,z.2]‖ = ‖z‖
    simp [Pi.norm_def,Fin.univ_succ,Prod.norm_def]
  have hDisk (z : P2) : E₂.symm z ∈ Disk ↔ z ∈ closedBall (0 : P2) 1 := by
    simp only [mem_closedBall,dist_zero_right,hnorm]
  have hRim (z : P2) : E₂.symm z ∈ Rim ↔ z ∈ sphere (0 : P2) 1 := by
    simp only [mem_sphere,dist_zero_right,hnorm]
  let p : P2 × T → X := fun z => j (E₂.symm z.1,z.2)
  have hpc : Continuous (fun z : closedBall (0 : P2) 1 × T => p (z.1,z.2)) := by
    exact hj.comp (((E₂.symm.continuous.comp
      (continuous_subtype_val.comp continuous_fst)).subtype_mk
      (fun z => (hDisk z.1).mpr z.1.property)).prodMk continuous_snd)
  have hproper' (z : P2) (hz : z ∈ closedBall (0 : P2) 1) (t : T) :
      p (z,t) ∈ S ↔ z ∈ sphere (0 : P2) 1 :=
    (hproper (E₂.symm z) ((hDisk z).mpr hz) t).trans (hRim z)
  have himage (A : Set P2) (B : Set V2)
      (hAB : ∀ z, E₂.symm z ∈ B ↔ z ∈ A) :
      p '' (A ×ˢ (univ : Set T)) = j '' (B ×ˢ (univ : Set T)) := by
    apply Subset.antisymm
    · rintro _ ⟨⟨z,t⟩,⟨hz,ht⟩,rfl⟩
      exact ⟨(E₂.symm z,t),⟨(hAB z).mpr hz,ht⟩,rfl⟩
    · rintro _ ⟨⟨z,t⟩,⟨hz,ht⟩,rfl⟩
      refine ⟨(E₂ z,t),⟨(hAB (E₂ z)).mp ?_,ht⟩,?_⟩
      · simpa only [E₂.symm_apply_apply] using hz
      · simp only [p,E₂.symm_apply_apply]
  have hfull := himage (closedBall (0 : P2) 1) Disk hDisk
  have hlateral := himage (sphere (0 : P2) 1) Rim hRim
  simpa only [hfull,hlateral] using
    s.exists_original_opposite_product_collar hR he hSR hU hSU p hpc hproper'

end PoincareConjecture.M76
