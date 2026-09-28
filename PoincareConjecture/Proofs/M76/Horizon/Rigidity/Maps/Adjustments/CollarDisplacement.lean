import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Maps.Adjustments.CollarCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Maps.OriginalLocalScalarExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLNeighborhoodExtension
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPLProduct

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

variable {X E F ι : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_supported_original_collar_scalar_plateau
    (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    {r : ℝ} (hr : 0 < r) (c : E × ℝ → X)
    (hc : PolyhedralPLInCharts e c (J.space ×ˢ Icc (-r) r))
    (hi : Topology.IsEmbedding (fun z : J.space ×ˢ Icc (-r) r => c z))
    (hopen : IsOpen (c '' (J.space ×ˢ Ioo (-(r / 2)) (r / 2))))
    (w : E → ℝ) (hw : FinitePiecewiseAffineOn w J.space) :
    ∃ (g : C(X, ℝ)) (C : Set X), IsCompact C ∧
      C ⊆ c '' (J.space ×ˢ Ioo (-(r / 2)) (r / 2)) ∧
      (∀ i, LocallyPiecewiseAffineOn (g ∘ (e i).symm) (e i).target) ∧
      (∀ x ∈ J.space, ∀ t ∈ Icc (-(r / 4)) (r / 4), g (c (x, t)) = w x) ∧
      (∀ x, x ∉ C → g x = 0) := by
  classical
  let S := J.space ×ˢ Icc (-r) r
  let U := c '' (J.space ×ˢ Ioo (-(r / 2)) (r / 2))
  have hsmall : J.space ×ˢ Ioo (-(r / 2)) (r / 2) ⊆ S := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact ⟨hx, by dsimp only at ht ⊢; constructor <;> linarith [ht.1, ht.2]⟩
  obtain ⟨q, hqleft, hqc, hqS, hqright, hqPL⟩ :=
    exists_original_PL_embedded_inverse e hcompat hc hi hopen (image_mono hsmall)
  have hqJ (y : X) (hy : y ∈ U) : (q y).1 ∈ J.space := (hqS hy).1
  obtain ⟨v, N, hN, hJN, hvPL, hvw⟩ := hw.exists_locallyPiecewiseAffine_extension
  let f := fun y : X => v (q y).1
  have hfc : ContinuousOn f U :=
    hvPL.continuousOn.comp hqc.fst (fun y hy => hJN (hqJ y hy))
  have hfPL (i : ι) : LocallyPiecewiseAffineOn (f ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' U) := by
    let T := (e i).target ∩ (e i).symm ⁻¹' U
    have hT : IsOpen T :=
      (e i).symm.continuousOn.isOpen_inter_preimage (e i).open_target hopen
    let a := (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap
    have hp := (locallyPiecewiseAffineOn_affine a isOpen_univ).comp (hqPL i)
    rw [preimage_univ, inter_univ] at hp
    exact (hvPL.comp hp).mono hT (fun y hy => ⟨hy, hJN (hqJ _ hy.2)⟩)
  let A := c '' (J.space ×ˢ Icc (-(r / 4)) (r / 4))
  have hAS : J.space ×ˢ Icc (-(r / 4)) (r / 4) ⊆ S := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact ⟨hx, by dsimp only at ht ⊢; constructor <;> linarith [ht.1, ht.2]⟩
  have hA : IsCompact A :=
    ((J.isCompact_space_of_finite hJ).prod isCompact_Icc).image_of_continuousOn
      (hc.continuousOn.mono hAS)
  have hAU : A ⊆ U := by
    rintro y ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    exact ⟨(x, t), ⟨hx, by dsimp only at ht ⊢; constructor <;> linarith [ht.1, ht.2]⟩, rfl⟩
  obtain ⟨b, hb⟩ := hA.bddAbove_image (hfc.mono hAU).abs
  have hbound (y : X) (hy : y ∈ A) : |f y| ≤ max b 0 + 1 := by
    have h := hb (mem_image_of_mem _ hy)
    have hm := le_max_left b 0
    linarith
  obtain ⟨g, C, hC, hCU, hgc, hgPL, hgf, hgbound, hgzero⟩ :=
    OpenPartialHomeomorph.exists_supported_PL_scalar_extension e hcompat hcover
      hA hopen hAU hfc hfPL (show 0 < max b 0 + 1 by positivity) hbound
  refine ⟨⟨g, hgc⟩, C, hC, hCU, hgPL, ?_, hgzero⟩
  intro x hx t ht
  change g (c (x, t)) = w x
  rw [hgf (show c (x, t) ∈ A from ⟨(x, t), ⟨hx, ht⟩, rfl⟩)]
  change v (q (c (x, t))).1 = w x
  rw [hqleft (hAS (show (x, t) ∈ J.space ×ˢ Icc (-(r / 4)) (r / 4) from ⟨hx, ht⟩))]
  exact hvw hx

theorem exists_supported_original_collar_scalar
    (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    {r : ℝ} (hr : 0 < r) (c : E × ℝ → X)
    (hc : PolyhedralPLInCharts e c (J.space ×ˢ Icc (-r) r))
    (hi : Topology.IsEmbedding (fun z : J.space ×ˢ Icc (-r) r => c z))
    (hopen : IsOpen (c '' (J.space ×ˢ Ioo (-(r / 2)) (r / 2))))
    (w : E → ℝ) (hw : FinitePiecewiseAffineOn w J.space) :
    ∃ (g : C(X, ℝ)) (C : Set X), IsCompact C ∧
      C ⊆ c '' (J.space ×ˢ Ioo (-(r / 2)) (r / 2)) ∧
      (∀ i, LocallyPiecewiseAffineOn (g ∘ (e i).symm) (e i).target) ∧
      (∀ x ∈ J.space, g (c (x, 0)) = w x) ∧
      (∀ x, x ∉ C → g x = 0) := by
  obtain ⟨g, C, hC, hCU, hgPL, hbase, hzero⟩ :=
    exists_supported_original_collar_scalar_plateau e hcompat hcover J hJ hr c hc hi hopen w hw
  exact ⟨g, C, hC, hCU, hgPL,
    fun x hx => hbase x hx 0 ⟨by linarith, by linarith⟩, hzero⟩

theorem exists_supported_original_collar_displacement_plateau
    (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    {r : ℝ} (hr : 0 < r) (c : E × ℝ → X)
    (hc : PolyhedralPLInCharts e c (J.space ×ˢ Icc (-r) r))
    (hi : Topology.IsEmbedding (fun z : J.space ×ˢ Icc (-r) r => c z))
    (hopen : IsOpen (c '' (J.space ×ˢ Ioo (-(r / 2)) (r / 2))))
    (w : E → ℝ × ℝ) (hw : FinitePiecewiseAffineOn w J.space) :
    ∃ (W : C(X, Fin 3 → ℝ)) (C : Set X), IsCompact C ∧
      C ⊆ c '' (J.space ×ˢ Ioo (-(r / 2)) (r / 2)) ∧
      (∀ i, LocallyPiecewiseAffineOn (W ∘ (e i).symm) (e i).target) ∧
      (∀ x ∈ J.space, ∀ t ∈ Icc (-(r / 4)) (r / 4),
        W (c (x, t)) = ![(w x).1, (w x).2, 0]) ∧
      (∀ x, W x 2 = 0) ∧ (∀ x, x ∉ C → W x = 0) := by
  obtain ⟨g₀, C₀, hC₀, hC₀U, hg₀PL, hg₀base, hg₀zero⟩ :=
    exists_supported_original_collar_scalar_plateau e hcompat hcover J hJ hr c hc hi hopen
      (fun x => (w x).1) (hw.postcomp (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap)
  obtain ⟨g₁, C₁, hC₁, hC₁U, hg₁PL, hg₁base, hg₁zero⟩ :=
    exists_supported_original_collar_scalar_plateau e hcompat hcover J hJ hr c hc hi hopen
      (fun x => (w x).2) (hw.postcomp (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap)
  let W : C(X, Fin 3 → ℝ) := ⟨fun x => ![g₀ x, g₁ x, 0], by
    apply continuous_pi
    intro j
    fin_cases j
    · exact g₀.continuous
    · exact g₁.continuous
    · exact continuous_const⟩
  refine ⟨W, C₀ ∪ C₁, hC₀.union hC₁, union_subset hC₀U hC₁U, ?_, ?_,
    fun _ => rfl, ?_⟩
  · intro i
    apply LocallyPiecewiseAffineOn.pi (e i).open_target
    intro j
    fin_cases j
    · exact hg₀PL i
    · exact hg₁PL i
    · exact locallyPiecewiseAffineOn_affine (ContinuousAffineMap.const ℝ F (0 : ℝ))
        (e i).open_target
  · intro x hx t ht
    change ![g₀ (c (x, t)), g₁ (c (x, t)), 0] = ![(w x).1, (w x).2, 0]
    rw [hg₀base x hx t ht, hg₁base x hx t ht]
  · intro x hx
    change ![g₀ x, g₁ x, 0] = 0
    rw [hg₀zero x (fun h => hx (Or.inl h)), hg₁zero x (fun h => hx (Or.inr h))]
    ext j
    fin_cases j <;> rfl

theorem exists_supported_original_collar_displacement
    (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    {r : ℝ} (hr : 0 < r) (c : E × ℝ → X)
    (hc : PolyhedralPLInCharts e c (J.space ×ˢ Icc (-r) r))
    (hi : Topology.IsEmbedding (fun z : J.space ×ˢ Icc (-r) r => c z))
    (hopen : IsOpen (c '' (J.space ×ˢ Ioo (-(r / 2)) (r / 2))))
    (w : E → ℝ × ℝ) (hw : FinitePiecewiseAffineOn w J.space) :
    ∃ (W : C(X, Fin 3 → ℝ)) (C : Set X), IsCompact C ∧
      C ⊆ c '' (J.space ×ˢ Ioo (-(r / 2)) (r / 2)) ∧
      (∀ i, LocallyPiecewiseAffineOn (W ∘ (e i).symm) (e i).target) ∧
      (∀ x ∈ J.space, W (c (x, 0)) = ![(w x).1, (w x).2, 0]) ∧
      (∀ x, W x 2 = 0) ∧ (∀ x, x ∉ C → W x = 0) := by
  obtain ⟨W, C, hC, hCU, hWPL, hbase, hnormal, hzero⟩ :=
    exists_supported_original_collar_displacement_plateau e hcompat hcover J hJ hr c hc hi hopen w hw
  exact ⟨W, C, hC, hCU, hWPL,
    fun x hx => hbase x hx 0 ⟨by linarith, by linarith⟩, hnormal, hzero⟩

end PoincareConjecture.M76
