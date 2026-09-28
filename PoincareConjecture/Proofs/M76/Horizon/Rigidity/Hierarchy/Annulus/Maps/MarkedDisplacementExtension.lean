import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Coverings.LiftedRimPL
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteTerminalPair
import PoincareConjecture.Proofs.M76.Mathlib.SupportedFinitePLExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLNeighborhoodExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Affine.Mathlib.ContinuousAffineSelection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem exists_original_marked_annulus_displacement_extension_within
    {X ι : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    (e : ι → OpenPartialHomeomorph X V3)
    {R : Set X} (heR : PLDomain e R)
    {j : (ℝ × ℝ) → X} (hj : PolyhedralPLInCharts e j Ann)
    (hji : Topology.IsEmbedding (fun x : Ann => j x))
    (hrim : ∀ x : Ann,
      depth 8 (x : ℝ × ℝ) = -1 ∨ depth 8 (x : ℝ × ℝ) = 1 ↔ j x ∈ frontier R)
    (w : (ℝ × ℝ) → V3) (hw : FinitePiecewiseAffineOn w Ann)
    (hw1 : ∀ x ∈ Ann, w x 1 = 0)
    (hwzero : ∀ x : Ann,
      depth 8 (x : ℝ × ℝ) = -1 ∨ depth 8 (x : ℝ × ℝ) = 1 → w x = 0)
    (U : Set X) (hU : IsOpen U) (hjU : ∀ x : Ann, j x ∈ U) :
    ∃ W : C(X, V3),
      (∀ i, LocallyPiecewiseAffineOn (W ∘ (e i).symm) (e i).target) ∧
      (∀ x : Ann, W (j x) = w x) ∧
      (∀ x ∈ frontier R, W x = 0) ∧ (∀ x, W x 1 = 0) ∧
      (∀ x, x ∉ U → W x = 0) := by
  classical
  obtain ⟨s, F, K, _, H, hFc, hFPL, hK, _, _, hKs, _, hHF, _, _⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_domain_finite_pair e heR.compatible
      heR.cover (N := univ) isCompact_univ (by simp)
  let E := s → ℝ × V3
  have hFK (x : X) : F x ∈ K.space := hKs.symm.subset ⟨x, mem_univ _, rfl⟩
  have hFi : Function.Injective F := by
    intro x y hxy
    have hHxy : H ⟨x, mem_univ _⟩ = H ⟨y, mem_univ _⟩ :=
      Subtype.ext ((hHF ⟨x, mem_univ _⟩).trans (hxy.trans (hHF ⟨y, mem_univ _⟩).symm))
    exact congrArg Subtype.val (H.injective hHxy)
  obtain ⟨O₀, hO₀, hFO₀⟩ :=
    (hFc.isClosedEmbedding hFi).isEmbedding.isInducing.isOpen_iff.mp hU
  obtain ⟨_, Q, _, _, _, hQ, _, hQs, _, _⟩ :=
    OpenPartialHomeomorph.exists_finite_PL_domain_image_pair e heR.cover hFc hFPL
      (isCompact_univ.of_isClosed_subset heR.closed (subset_univ R)) hFi.injOn heR.halfspace
  have hwcopy := hw
  obtain ⟨J, hJ, hJs, _⟩ := hwcopy
  have hjJ : PolyhedralPLInCharts e j J.space := hJs ▸ hj
  have hf : FinitePiecewiseAffineOn (F ∘ j) Ann := by
    simpa only [hJs] using hjJ.finitePiecewiseAffineOn_comp J hJ hFPL
  have hfi : InjOn (F ∘ j) Ann := by
    intro x hx y hy heq
    exact congrArg Subtype.val (hji.injective
      (show (fun x : Ann => j x) ⟨x, hx⟩ = (fun x : Ann => j x) ⟨y, hy⟩ from hFi heq))
  obtain ⟨B, hB, hBval⟩ := hf.exists_homeomorph_image hfi
  obtain ⟨inv, hinv, hinvval⟩ := hB.symm
  let S : Set E := (F ∘ j) '' Ann
  have hinvS : MapsTo inv S Ann := by
    intro y hy
    rw [← hinvval ⟨y, hy⟩]
    exact (B.symm ⟨y, hy⟩).property
  have hinvleft (x : Ann) : inv (F (j x)) = x := by
    have h := hinvval (B x)
    rw [B.symm_apply_apply, hBval] at h
    exact h.symm
  let v : E → V3 := S.indicator (w ∘ inv)
  have hvS : FinitePiecewiseAffineOn v S :=
    (hw.comp hinv hinvS).congr (fun x hx => (indicator_of_mem hx _).symm)
  have hvQ (y : E) (hy : y ∈ Q.space) : v y = 0 := by
    by_cases hyS : y ∈ S
    · obtain ⟨x, hx, hxy⟩ := hyS
      obtain ⟨z, hz, hzy⟩ := hQs.subset hy
      have hjx : j x = z := hFi (hxy.trans hzy.symm)
      have hxrim := (hrim ⟨x, hx⟩).mpr (hjx ▸ hz)
      rw [show y = F (j x) from hxy.symm]
      dsimp only [v]
      rw [indicator_of_mem (show F (j x) ∈ S from ⟨x, hx, rfl⟩)]
      change w (inv (F (j x))) = 0
      rw [hinvleft ⟨x, hx⟩]
      exact hwzero ⟨x, hx⟩ hxrim
    · exact indicator_of_notMem hyS _
  have hvQPL : FinitePiecewiseAffineOn v Q.space :=
    (Q.affineOnFaces_affine (ContinuousAffineMap.const ℝ E (0 : V3))).finitePiecewiseAffineOn hQ
      |>.congr (fun x hx => (hvQ x hx).symm)
  have hSK : S ∪ Q.space ⊆ K.space := by
    rintro y (⟨x, _, rfl⟩ | hy)
    · exact hFK (j x)
    · obtain ⟨x, _, rfl⟩ := hQs.subset hy
      exact hFK x
  have hSO₀ : S ⊆ O₀ := by
    rintro _ ⟨x, hx, rfl⟩
    change j x ∈ F ⁻¹' O₀
    rw [hFO₀]
    exact hjU ⟨x, hx⟩
  obtain ⟨g, hg, hgv, hgO₀, _⟩ :=
    (finitePiecewiseAffineOn_union hvS hvQPL).exists_supported_extension_of_eq_zero_off
      K hK hSK hvS.isCompact (fun x _ hx => indicator_of_notMem hx _) hO₀ hSO₀
  obtain ⟨g', O, hO, hKO, hg'PL, hg'g⟩ := hg.exists_locallyPiecewiseAffine_extension
  have hFg'c : Continuous (g' ∘ F) :=
    hg'PL.continuousOn.comp_continuous hFc (fun x => hKO (hFK x))
  have hFg'PL (i : ι) : LocallyPiecewiseAffineOn ((g' ∘ F) ∘ (e i).symm) (e i).target := by
    have hh := hg'PL.comp (hFPL i)
    apply (hh.mono (e i).open_target (fun x hx => ⟨hx, hKO (hFK _)⟩)).congr
    intro x hx
    rfl
  let W : C(X, V3) := ⟨fun x => ![g' (F x) 0, 0, g' (F x) 2], by
    apply continuous_pi
    intro k
    fin_cases k
    · change Continuous (fun x => g' (F x) 0)
      exact (continuous_apply 0).comp hFg'c
    · exact continuous_const
    · change Continuous (fun x => g' (F x) 2)
      exact (continuous_apply 2).comp hFg'c⟩
  have hbase (x : Ann) : g' (F (j x)) = w x := by
    rw [hg'g (hFK _), hgv (Or.inl (show F (j x) ∈ S from ⟨x, x.property, rfl⟩))]
    dsimp only [v]
    rw [indicator_of_mem (show F (j x) ∈ S from ⟨x, x.property, rfl⟩)]
    change w (inv (F (j x))) = w x
    rw [hinvleft x]
  have hfront (x : X) (hx : x ∈ frontier R) : g' (F x) = 0 := by
    have hFxQ : F x ∈ Q.space := hQs.symm.subset ⟨x, hx, rfl⟩
    rw [hg'g (hFK x), hgv (Or.inr hFxQ), hvQ _ hFxQ]
  refine ⟨W, ?_, ?_, ?_, (fun _ => rfl), ?_⟩
  · intro i
    apply LocallyPiecewiseAffineOn.pi (e i).open_target
    intro k
    fin_cases k
    · have hh := (locallyPiecewiseAffineOn_affine
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).toContinuousAffineMap
        isOpen_univ).comp (hFg'PL i)
      rw [preimage_univ, inter_univ] at hh
      exact hh.congr (fun _ _ => rfl)
    · exact locallyPiecewiseAffineOn_affine (ContinuousAffineMap.const ℝ V3 (0 : ℝ))
        (e i).open_target
    · have hh := (locallyPiecewiseAffineOn_affine
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2).toContinuousAffineMap
        isOpen_univ).comp (hFg'PL i)
      rw [preimage_univ, inter_univ] at hh
      exact hh.congr (fun _ _ => rfl)
  · intro x
    change ![g' (F (j x)) 0, 0, g' (F (j x)) 2] = w x
    rw [hbase]
    ext k
    fin_cases k
    · rfl
    · exact (hw1 x x.property).symm
    · rfl
  · intro x hx
    change ![g' (F x) 0, 0, g' (F x) 2] = 0
    rw [hfront x hx]
    ext k
    fin_cases k <;> rfl
  · intro x hx
    have hFx : F x ∉ O₀ := by
      change x ∉ F ⁻¹' O₀
      rwa [hFO₀]
    change ![g' (F x) 0, 0, g' (F x) 2] = 0
    rw [hg'g (hFK x), hgO₀ _ hFx]
    ext k
    fin_cases k <;> rfl

theorem exists_original_marked_annulus_displacement_extension
    {X ι : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    (e : ι → OpenPartialHomeomorph X V3)
    {R : Set X} (heR : PLDomain e R)
    {j : (ℝ × ℝ) → X} (hj : PolyhedralPLInCharts e j Ann)
    (hji : Topology.IsEmbedding (fun x : Ann => j x))
    (hrim : ∀ x : Ann,
      depth 8 (x : ℝ × ℝ) = -1 ∨ depth 8 (x : ℝ × ℝ) = 1 ↔ j x ∈ frontier R)
    (w : (ℝ × ℝ) → V3) (hw : FinitePiecewiseAffineOn w Ann)
    (hw1 : ∀ x ∈ Ann, w x 1 = 0)
    (hwzero : ∀ x : Ann,
      depth 8 (x : ℝ × ℝ) = -1 ∨ depth 8 (x : ℝ × ℝ) = 1 → w x = 0) :
    ∃ W : C(X, V3),
      (∀ i, LocallyPiecewiseAffineOn (W ∘ (e i).symm) (e i).target) ∧
      (∀ x : Ann, W (j x) = w x) ∧
      (∀ x ∈ frontier R, W x = 0) ∧ (∀ x, W x 1 = 0) := by
  obtain ⟨W, hW, hbase, hfront, hsecond, _⟩ :=
    exists_original_marked_annulus_displacement_extension_within e heR hj hji hrim
      w hw hw1 hwzero univ isOpen_univ (fun _ => mem_univ _)
  exact ⟨W, hW, hbase, hfront, hsecond⟩

private theorem locallyPiecewiseAffineOn_selection_zero
    {f g : V3 → V3} {U : Set V3} (hf : LocallyPiecewiseAffineOn f U)
    (hg : ContinuousOn g U) (hselect : ∀ x ∈ U, g x = f x ∨ g x = 0) :
    LocallyPiecewiseAffineOn g U := by
  intro x hx
  obtain ⟨K, hK, hxK, hKU, hfK⟩ := hf x hx
  have hzero : FinitePiecewiseAffineOn (fun _ : V3 => (0 : V3)) K.space :=
    (K.affineOnFaces_affine (ContinuousAffineMap.const ℝ V3 (0 : V3))).finitePiecewiseAffineOn hK
  obtain ⟨J, hJ, hJK, hgJ⟩ := (hfK.finitePiecewiseAffineOn hK).continuous_selection_pi
    hzero (hg.mono hKU) (fun y hy => hselect y (hKU hy))
  exact ⟨J, hJ, hJK.symm ▸ hxK, hJK ▸ hKU, hgJ⟩

theorem exists_original_retained_annulus_displacement_extension_within
    {X ι : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    (e : ι → OpenPartialHomeomorph X V3)
    {R : Set X} (heR : PLDomain e R)
    {j : (ℝ × ℝ) → X} (hj : PolyhedralPLInCharts e j Ann)
    (hji : Topology.IsEmbedding (fun x : Ann => j x))
    (hjR : MapsTo j Ann R)
    (hrim : ∀ x : Ann,
      depth 8 (x : ℝ × ℝ) = -1 ∨ depth 8 (x : ℝ × ℝ) = 1 ↔ j x ∈ frontier R)
    (w : (ℝ × ℝ) → V3) (hw : FinitePiecewiseAffineOn w Ann)
    (hw1 : ∀ x ∈ Ann, w x 1 = 0)
    (hwzero : ∀ x : Ann,
      depth 8 (x : ℝ × ℝ) = -1 ∨ depth 8 (x : ℝ × ℝ) = 1 → w x = 0)
    (U : Set X) (hU : IsOpen U) (hjU : ∀ x : Ann, j x ∈ U) :
    ∃ W : C(X, V3),
      (∀ i, LocallyPiecewiseAffineOn (W ∘ (e i).symm) (e i).target) ∧
      (∀ x : Ann, W (j x) = w x) ∧
      (∀ x ∈ frontier R, W x = 0) ∧ (∀ x, W x 1 = 0) ∧
      (∀ x, x ∉ R → W x = 0) ∧ (∀ x, x ∉ U → W x = 0) := by
  classical
  obtain ⟨W, hWPL, hWbase, hWfront, hW1, hWoffU⟩ :=
    exists_original_marked_annulus_displacement_extension_within e heR hj hji hrim
      w hw hw1 hwzero U hU hjU
  let V : C(X, V3) := ⟨R.piecewise W (fun _ => 0),
    Continuous.piecewise hWfront W.continuous continuous_const⟩
  have hVselect (x : X) : V x = W x ∨ V x = 0 := by
    by_cases hx : x ∈ R
    · exact Or.inl (piecewise_eq_of_mem R W (fun _ => 0) hx)
    · exact Or.inr (piecewise_eq_of_notMem R W (fun _ => 0) hx)
  refine ⟨V, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact locallyPiecewiseAffineOn_selection_zero (hWPL i)
      (V.continuous.comp_continuousOn (e i).continuousOn_symm)
      (fun x _ => hVselect ((e i).symm x))
  · intro x
    change R.piecewise W (fun _ => 0) (j x) = w x
    rw [piecewise_eq_of_mem R W (fun _ => 0) (hjR x.property), hWbase x]
  · intro x hx
    exact (hVselect x).elim (fun h => h.trans (hWfront x hx)) id
  · intro x
    exact (hVselect x).elim (fun h => (congrFun h 1).trans (hW1 x)) (fun h => congrFun h 1)
  · intro x hx
    exact piecewise_eq_of_notMem R W (fun _ => 0) hx
  · intro x hx
    exact (hVselect x).elim (fun h => h.trans (hWoffU x hx)) id

theorem exists_original_retained_annulus_displacement_extension
    {X ι : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    (e : ι → OpenPartialHomeomorph X V3)
    {R : Set X} (heR : PLDomain e R)
    {j : (ℝ × ℝ) → X} (hj : PolyhedralPLInCharts e j Ann)
    (hji : Topology.IsEmbedding (fun x : Ann => j x))
    (hjR : MapsTo j Ann R)
    (hrim : ∀ x : Ann,
      depth 8 (x : ℝ × ℝ) = -1 ∨ depth 8 (x : ℝ × ℝ) = 1 ↔ j x ∈ frontier R)
    (w : (ℝ × ℝ) → V3) (hw : FinitePiecewiseAffineOn w Ann)
    (hw1 : ∀ x ∈ Ann, w x 1 = 0)
    (hwzero : ∀ x : Ann,
      depth 8 (x : ℝ × ℝ) = -1 ∨ depth 8 (x : ℝ × ℝ) = 1 → w x = 0) :
    ∃ W : C(X, V3),
      (∀ i, LocallyPiecewiseAffineOn (W ∘ (e i).symm) (e i).target) ∧
      (∀ x : Ann, W (j x) = w x) ∧
      (∀ x ∈ frontier R, W x = 0) ∧ (∀ x, W x 1 = 0) ∧
      (∀ x, x ∉ R → W x = 0) := by
  obtain ⟨W, hW, hbase, hfront, hsecond, houtside, _⟩ :=
    exists_original_retained_annulus_displacement_extension_within e heR hj hji hjR hrim
      w hw hw1 hwzero univ isOpen_univ (fun _ => mem_univ _)
  exact ⟨W, hW, hbase, hfront, hsecond, houtside⟩

end PoincareConjecture.M76
