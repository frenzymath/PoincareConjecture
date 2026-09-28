import PoincareConjecture.Proofs.M25.Topology3D.Sphere2.CylinderCollarProfile
import PoincareConjecture.Proofs.M25.AppA_21_Local.CylinderCoordinates






set_option autoImplicit false
open Set Filter
open scoped Manifold ContDiff Topology
universe u
namespace PoincareConjecture.M25.Topology3D
section HeightMap
variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} (T : OpenCylinderModel U)
open scoped Classical in

noncomputable def cylinderHeightMap (φ : ℝ → ℝ) (x : M) : M :=
  if x ∈ U then T.coordinate ((T.inverse x).1, φ (T.inverse x).2) else x

theorem cylinderHeightMap_of_not_mem (φ : ℝ → ℝ) {x : M} (hx : x ∉ U) :
    cylinderHeightMap T φ x = x := by
  simp [cylinderHeightMap, hx]

theorem cylinderHeightMap_of_mem (φ : ℝ → ℝ) {x : M} (hx : x ∈ U) :
    cylinderHeightMap T φ x = T.coordinate ((T.inverse x).1, φ (T.inverse x).2) := by
  simp [cylinderHeightMap, hx]

theorem cylinderModel_coordinate_mem {z : RoundCylinderSpace}
    (hz : z ∈ (univ : Set UnitTwoSphere) ×ˢ Ioo (0 : ℝ) 1) : T.coordinate z ∈ U := by
  have hm := (T.homeomorph (z.1, ⟨z.2, hz.2⟩)).property
  rwa [T.coordinate_eq] at hm

theorem cylinderHeightMap_coordinate (φ : ℝ → ℝ) {z : RoundCylinderSpace}
    (hz : z ∈ (univ : Set UnitTwoSphere) ×ˢ Ioo (0 : ℝ) 1) :
    cylinderHeightMap T φ (T.coordinate z) = T.coordinate (z.1, φ z.2) := by
  rw [cylinderHeightMap_of_mem T φ (cylinderModel_coordinate_mem T hz), T.left_inverse hz]

theorem tail_subset_Ioo (side : Bool) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    (if side then Ioo a 1 else Ioo 0 a) ⊆ Ioo (0 : ℝ) 1 := by
  cases side
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact Ioo_subset_Ioo le_rfl ha.2.le
  · simp only [↓reduceIte]
    exact Ioo_subset_Ioo ha.1.le le_rfl

theorem cylinderHeightMap_image (φ : ℝ → ℝ) {J : Set ℝ} (hJ : φ '' Ioo 0 1 = J) :
    cylinderHeightMap T φ '' U = T.coordinate '' ((univ : Set UnitTwoSphere) ×ˢ J) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hz := T.inverse_mem x hx
    rw [cylinderHeightMap_of_mem T φ hx]
    refine ⟨((T.inverse x).1, φ (T.inverse x).2), ⟨mem_univ _, ?_⟩, rfl⟩
    rw [← hJ]
    exact ⟨(T.inverse x).2, hz.2, rfl⟩
  · rintro ⟨⟨s, h'⟩, ⟨-, hh'⟩, rfl⟩
    rw [← hJ] at hh'
    obtain ⟨h, hh, hφ⟩ := hh'
    change φ h = h' at hφ
    subst hφ
    have hz : ((s, h) : RoundCylinderSpace) ∈ (univ : Set UnitTwoSphere) ×ˢ Ioo (0 : ℝ) 1 :=
      ⟨mem_univ _, hh⟩
    exact ⟨T.coordinate (s, h), cylinderModel_coordinate_mem T hz,
      cylinderHeightMap_coordinate T φ hz⟩

theorem height_mem_of_mem_tail (side : Bool) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    {y : M} (hy : y ∈ T.tail side a) :
    (T.inverse y).2 ∈ (if side then Ioo a 1 else Ioo 0 a) := by
  obtain ⟨z, ⟨-, hz⟩, rfl⟩ := hy
  rw [T.left_inverse ⟨mem_univ _, tail_subset_Ioo side ha hz⟩]
  exact hz
variable [T2Space M] {C : Set M} (hU : IsOpen U) (hC : IsOpen C) (side : Bool) {a : ℝ}
  (ha : a ∈ Ioo (0 : ℝ) 1) (htail : T.tail side a ⊆ C) (hoverlap : C ∩ U ⊆ T.tail side a)
  (φ : ℝ ≃ₘ[ℝ] ℝ) {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1)
  (hJ : φ '' Ioo 0 1 = (if side then Ioo a 1 else Ioo 0 a))
  (hfix : ∀ h : ℝ, (if side then b ≤ h else h ≤ b) → φ h = h)
include T hU hC side ha htail hoverlap φ hb hJ hfix in
private theorem exists_collar_local_decomposition :
    ∃ (l u : ℝ) (K Q U₀ : Set M),
      0 < l ∧ l < u ∧ u < 1 ∧
      IsOpen Q ∧ IsOpen U₀ ∧ IsOpen (T.tail side a) ∧
      closure K ⊆ U ∧ Q ⊆ T.tail side a ∧
      U₀ ∪ U = C ∪ U ∧ U₀ ∪ T.tail side a = C ∧
      (∀ x ∈ U₀, cylinderHeightMap T φ x = x) ∧
      (∀ x ∈ U₀, cylinderHeightMap T φ.symm x = x) := by
  have htailU : T.tail side a ⊆ U := openCylinderModel_tail_subset T side ha
  have hinter : C ∩ U = T.tail side a := by
    apply Subset.antisymm hoverlap
    intro x hx
    exact ⟨htail hx, htailU hx⟩
  let e : OpenPartialHomeomorph RoundCylinderSpace M :=
    { toFun := T.coordinate
      invFun := T.inverse
      source := univ ×ˢ Ioo (0 : ℝ) 1
      target := U
      map_source' := by
        intro z hz
        exact cylinderModel_coordinate_mem T hz
      map_target' := T.inverse_mem
      left_inv' := T.left_inverse
      right_inv' := T.right_inverse
      open_source := isOpen_univ.prod isOpen_Ioo
      open_target := hU
      continuousOn_toFun := T.coordinate_smooth.continuousOn
      continuousOn_invFun := T.inverse_smooth.continuousOn }
  have htailopen : IsOpen (T.tail side a) := by
    dsimp [OpenCylinderModel.tail, e]
    apply e.isOpen_image_of_subset_source
    · cases side <;> simp only [Bool.false_eq_true, ↓reduceIte, isOpen_univ, isOpen_Ioo,
        IsOpen.prod]
    · intro z hz
      exact ⟨mem_univ _, (tail_subset_Ioo side ha hz.2).1,
        (tail_subset_Ioo side ha hz.2).2⟩
  have hinvfix (h : ℝ) (hh : (if side then b ≤ h else h ≤ b)) :
      φ.symm h = h := by
    have heq := congrArg φ.symm (hfix h hh)
    simpa only [Diffeomorph.symm_apply_apply] using heq.symm
  cases side with
  | false =>
      let l : ℝ := min (a / 2) b
      let u : ℝ := a
      let K : Set M := T.coordinate '' (univ ×ˢ Ioo l u)
      let Q : Set M := T.coordinate '' (univ ×ˢ Ioo (0 : ℝ) l)
      let U₀ : Set M := (C \ closure K) ∪ Q
      have hl : 0 < l := lt_min (by linarith [ha.1]) hb.1
      have hlu : l < u := lt_of_le_of_lt (min_le_left _ _) (by linarith [ha.1])
      have hu : u < 1 := ha.2
      have hQopen : IsOpen Q := by
        dsimp [Q, e]
        apply e.isOpen_image_of_subset_source
        · exact isOpen_univ.prod isOpen_Ioo
        · intro z hz
          have hl1 : l < 1 := lt_of_le_of_lt (min_le_left _ _) (by linarith [ha.2])
          exact ⟨mem_univ _, hz.2.1, hz.2.2.trans hl1⟩
      have hslab : IsCompact (T.coordinate '' (univ ×ˢ Icc l u)) :=
        openCylinderModel_isCompact_coordinate_slab T hl hu
      have hKcl : closure K ⊆ U := by
        apply (closure_minimal (image_mono (prod_mono subset_rfl Ioo_subset_Icc_self))
          hslab.isClosed).trans
        exact openCylinderModel_coordinate_slab_subset T hl hu
      have hQtail : Q ⊆ T.tail false a := by
        intro x hx
        rcases hx with ⟨z, hz, rfl⟩
        rw [OpenCylinderModel.tail]
        have hla : l < a := lt_of_le_of_lt (min_le_left _ _) (by linarith [ha.1])
        have hz1 : z.2 < a := hz.2.2.trans hla
        exact ⟨z, ⟨mem_univ _, hz.2.1, hz1⟩, rfl⟩
      have hU₀open : IsOpen U₀ :=
        (hC.sdiff isClosed_closure).union hQopen
      have hcover : U₀ ∪ U = C ∪ U := by
        apply Subset.antisymm
        · intro x hx
          rcases hx with hx | hx
          · rcases hx with hx | hx
            · exact Or.inl hx.1
            · exact Or.inr (htailU (hQtail hx))
          · exact Or.inr hx
        · intro x hx
          rcases hx with hx | hx
          · by_cases hxU : x ∈ U
            · exact Or.inr hxU
            · exact Or.inl (Or.inl ⟨hx, fun hcl => hxU (hKcl hcl)⟩)
          · exact Or.inr hx
      have hcover' : U₀ ∪ T.tail false a = C := by
        apply Subset.antisymm
        · intro x hx
          rcases hx with hx | hx
          · change x ∈ C \ closure K ∨ x ∈ Q at hx
            rcases hx with hx | hx
            · exact hx.1
            · exact htail (hQtail hx)
          · exact htail hx
        · intro x hx
          by_cases hxt : x ∈ T.tail false a
          · exact Or.inr hxt
          · exact Or.inl (Or.inl ⟨hx, fun hcl => hxt (by
              rw [← hinter]
              exact ⟨hx, hKcl hcl⟩)⟩)
      have hKmem (x : M) (hxU : x ∈ U) (hs : (T.inverse x).2 ∈ Ioo l u) :
          x ∈ K := by
        exact ⟨T.inverse x, ⟨mem_univ _, hs.1, hs.2⟩, T.right_inverse hxU⟩
      have hfixU₀ (x : M) (hx : x ∈ U₀) (hxU : x ∈ U) :
          φ (T.inverse x).2 = (T.inverse x).2 := by
        change x ∈ C \ closure K ∨ x ∈ Q at hx
        rcases hx with hx | hx
        · have hxt : x ∈ T.tail false a := by
            rw [← hinter]
            exact ⟨hx.1, hxU⟩
          have hi := (openCylinderModel_mem_tail_iff T false ha x).mp hxt
          have hsnot : (T.inverse x).2 ∉ Ioo l u :=
            fun hs => hx.2 (subset_closure (hKmem x hxU hs))
          have hi' : (T.inverse x).2 < a := by simpa using hi.2
          have hle : (T.inverse x).2 ≤ l := by
            by_contra hn
            exact hsnot ⟨lt_of_not_ge hn, hi'⟩
          exact hfix _ (hle.trans (min_le_right (a / 2) b))
        · rcases hx with ⟨z, hz, rfl⟩
          have hl1 : l < 1 := lt_of_le_of_lt (min_le_left _ _) (by linarith [ha.2])
          rw [T.left_inverse ⟨mem_univ _, hz.2.1, hz.2.2.trans hl1⟩]
          exact hfix _ (hz.2.2.le.trans (min_le_right (a / 2) b))
      have hfixInvU₀ (x : M) (hx : x ∈ U₀) :
          cylinderHeightMap T φ.symm x = x := by
        change x ∈ C \ closure K ∨ x ∈ Q at hx
        by_cases hxt : x ∈ T.tail false a
        · rw [cylinderHeightMap_of_mem T φ.symm (htailU hxt)]
          have hi := (openCylinderModel_mem_tail_iff T false ha x).mp hxt
          have hsnot : (T.inverse x).2 ∉ Ioo l u := by
            intro hs
            rcases hx with hx | hx
            · exact hx.2 (subset_closure (hKmem x (htailU hxt) hs))
            · rcases hx with ⟨z, hz, rfl⟩
              have hl1 : l < 1 := lt_of_le_of_lt (min_le_left _ _) (by linarith [ha.2])
              rw [T.left_inverse ⟨mem_univ _, hz.2.1, hz.2.2.trans hl1⟩] at hs
              exact (not_lt_of_ge hz.2.2.le) hs.1
          have hi' : (T.inverse x).2 < a := by simpa using hi.2
          have hle : (T.inverse x).2 ≤ l := by
            by_contra hn
            exact hsnot ⟨lt_of_not_ge hn, hi'⟩
          have hh : (if false then b ≤ (T.inverse x).2 else (T.inverse x).2 ≤ b) := by
            simp only [Bool.false_eq_true, ↓reduceIte]
            linarith [hle, min_le_right (a / 2) b]
          rw [hinvfix _ hh]
          exact T.right_inverse (htailU hxt)
        · have hxout : x ∉ U := by
            intro hxU
            have hxc : x ∈ C := by
              rcases hx with hx | hx
              · exact hx.1
              · exact htail (hQtail hx)
            exact hxt (by
              rw [← hinter]
              exact ⟨hxc, hxU⟩)
          exact cylinderHeightMap_of_not_mem T φ.symm hxout
      refine ⟨l, u, K, Q, U₀, hl, hlu, hu, hQopen, hU₀open, htailopen,
        hKcl, hQtail, hcover, hcover', ?_, hfixInvU₀⟩
      intro x hx
      by_cases hxU : x ∈ U
      · rw [cylinderHeightMap_of_mem T φ hxU, hfixU₀ x hx hxU]
        exact T.right_inverse hxU
      · exact cylinderHeightMap_of_not_mem T φ hxU
  | true =>
      let l : ℝ := a / 2
      let u : ℝ := max b ((1 + a) / 2)
      let K : Set M := T.coordinate '' (univ ×ˢ Ioo l u)
      let Q : Set M := T.coordinate '' (univ ×ˢ Ioo u (1 : ℝ))
      let U₀ : Set M := (C \ closure K) ∪ Q
      have hl : 0 < l := by dsimp [l]; linarith [ha.1]
      have hlu : l < u := by
        exact lt_of_lt_of_le (by dsimp [l]; linarith) (le_max_right _ _)
      have hu : u < 1 := max_lt hb.2 (by linarith [ha.2])
      have hQopen : IsOpen Q := by
        dsimp [Q, e]
        apply e.isOpen_image_of_subset_source
        · exact isOpen_univ.prod isOpen_Ioo
        · intro z hz
          have hu0 : 0 < u := lt_of_lt_of_le hb.1 (le_max_left _ _)
          exact ⟨mem_univ _, hu0.trans hz.2.1, hz.2.2⟩
      have hslab : IsCompact (T.coordinate '' (univ ×ˢ Icc l u)) :=
        openCylinderModel_isCompact_coordinate_slab T hl hu
      have hKcl : closure K ⊆ U := by
        apply (closure_minimal (image_mono (prod_mono subset_rfl Ioo_subset_Icc_self))
          hslab.isClosed).trans
        exact openCylinderModel_coordinate_slab_subset T hl hu
      have hQtail : Q ⊆ T.tail true a := by
        intro x hx
        rcases hx with ⟨z, hz, rfl⟩
        rw [OpenCylinderModel.tail]
        have hau : a < u := lt_of_lt_of_le (by linarith [ha.2]) (le_max_right _ _)
        exact ⟨z, ⟨mem_univ _, hau.trans hz.2.1, hz.2.2⟩, rfl⟩
      have hU₀open : IsOpen U₀ :=
        (hC.sdiff isClosed_closure).union hQopen
      have hcover : U₀ ∪ U = C ∪ U := by
        apply Subset.antisymm
        · intro x hx
          rcases hx with hx | hx
          · rcases hx with hx | hx
            · exact Or.inl hx.1
            · exact Or.inr (htailU (hQtail hx))
          · exact Or.inr hx
        · intro x hx
          rcases hx with hx | hx
          · by_cases hxU : x ∈ U
            · exact Or.inr hxU
            · exact Or.inl (Or.inl ⟨hx, fun hcl => hxU (hKcl hcl)⟩)
          · exact Or.inr hx
      have hcover' : U₀ ∪ T.tail true a = C := by
        apply Subset.antisymm
        · intro x hx
          rcases hx with hx | hx
          · change x ∈ C \ closure K ∨ x ∈ Q at hx
            rcases hx with hx | hx
            · exact hx.1
            · exact htail (hQtail hx)
          · exact htail hx
        · intro x hx
          by_cases hxt : x ∈ T.tail true a
          · exact Or.inr hxt
          · exact Or.inl (Or.inl ⟨hx, fun hcl => hxt (by
              rw [← hinter]
              exact ⟨hx, hKcl hcl⟩)⟩)
      have hKmem (x : M) (hxU : x ∈ U) (hs : (T.inverse x).2 ∈ Ioo l u) :
          x ∈ K := by
        exact ⟨T.inverse x, ⟨mem_univ _, hs.1, hs.2⟩, T.right_inverse hxU⟩
      have hfixU₀ (x : M) (hx : x ∈ U₀) (hxU : x ∈ U) :
          φ (T.inverse x).2 = (T.inverse x).2 := by
        change x ∈ C \ closure K ∨ x ∈ Q at hx
        rcases hx with hx | hx
        · have hxt : x ∈ T.tail true a := by
            rw [← hinter]
            exact ⟨hx.1, hxU⟩
          have hi := (openCylinderModel_mem_tail_iff T true ha x).mp hxt
          have hsnot : (T.inverse x).2 ∉ Ioo l u :=
            fun hs => hx.2 (subset_closure (hKmem x hxU hs))
          have hi' : a < (T.inverse x).2 := by simpa using hi.2
          have hla : l < a := by dsimp [l]; linarith [ha.1]
          have hge : u ≤ (T.inverse x).2 := by
            by_contra hn
            exact hsnot ⟨hla.trans hi', lt_of_not_ge hn⟩
          exact hfix _ ((le_max_left b ((1 + a) / 2)).trans hge)
        · rcases hx with ⟨z, hz, rfl⟩
          have hu0 : 0 < u := lt_of_lt_of_le hb.1 (le_max_left _ _)
          rw [T.left_inverse ⟨mem_univ _, hu0.trans hz.2.1, hz.2.2⟩]
          have hbu : b ≤ u := le_max_left _ _
          exact hfix _ (hbu.trans hz.2.1.le)
      have hfixInvU₀ (x : M) (hx : x ∈ U₀) :
          cylinderHeightMap T φ.symm x = x := by
        change x ∈ C \ closure K ∨ x ∈ Q at hx
        by_cases hxt : x ∈ T.tail true a
        · rw [cylinderHeightMap_of_mem T φ.symm (htailU hxt)]
          have hi := (openCylinderModel_mem_tail_iff T true ha x).mp hxt
          have hsnot : (T.inverse x).2 ∉ Ioo l u := by
            intro hs
            rcases hx with hx | hx
            · exact hx.2 (subset_closure (hKmem x (htailU hxt) hs))
            · rcases hx with ⟨z, hz, rfl⟩
              have hu0 : 0 < u := lt_of_lt_of_le hb.1 (le_max_left _ _)
              rw [T.left_inverse ⟨mem_univ _, hu0.trans hz.2.1, hz.2.2⟩] at hs
              exact (not_lt_of_ge hs.2.le) hz.2.1
          have hi' : a < (T.inverse x).2 := by simpa using hi.2
          have hla : l < a := by dsimp [l]; linarith [ha.1]
          have hge : u ≤ (T.inverse x).2 := by
            by_contra hn
            exact hsnot ⟨hla.trans hi', lt_of_not_ge hn⟩
          have hh : (if true then b ≤ (T.inverse x).2 else (T.inverse x).2 ≤ b) := by
            simp only [↓reduceIte]
            linarith [hge, le_max_left b ((1 + a) / 2)]
          rw [hinvfix _ hh]
          exact T.right_inverse (htailU hxt)
        · have hxout : x ∉ U := by
            intro hxU
            have hxc : x ∈ C := by
              rcases hx with hx | hx
              · exact hx.1
              · exact htail (hQtail hx)
            exact hxt (by
              rw [← hinter]
              exact ⟨hxc, hxU⟩)
          exact cylinderHeightMap_of_not_mem T φ.symm hxout
      refine ⟨l, u, K, Q, U₀, hl, hlu, hu, hQopen, hU₀open, htailopen,
        hKcl, hQtail, hcover, hcover', ?_, hfixInvU₀⟩
      intro x hx
      by_cases hxU : x ∈ U
      · rw [cylinderHeightMap_of_mem T φ hxU, hfixU₀ x hx hxU]
        exact T.right_inverse hxU
      · exact cylinderHeightMap_of_not_mem T φ hxU
omit [T2Space M] in
private theorem continuousOn_cylinderHeightMap_on
    (ψ : ℝ ≃ₘ[ℝ] ℝ) {S : Set M} (hS : S ⊆ U)
    (hψ : ∀ x ∈ S, ψ (T.inverse x).2 ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (cylinderHeightMap T ψ) S := by
  have hi : ContinuousOn T.inverse S := T.inverse_smooth.continuousOn.mono hS
  have hfst : ContinuousOn (fun x : M => (T.inverse x).1) S :=
    continuous_fst.continuousOn.comp hi (fun _ _ => mem_univ _)
  have hsnd : ContinuousOn (fun x : M => (T.inverse x).2) S :=
    continuous_snd.continuousOn.comp hi (fun _ _ => mem_univ _)
  have hheight : ContinuousOn (fun x : M => ψ (T.inverse x).2) S :=
    ψ.continuous.continuousOn.comp hsnd (fun _ _ => mem_univ _)
  have hpair : ContinuousOn
      (fun x : M => ((T.inverse x).1, ψ (T.inverse x).2)) S := hfst.prodMk hheight
  have hmap := T.coordinate_smooth.continuousOn.comp hpair (fun x hx =>
    ⟨mem_univ _, hψ x hx⟩)
  exact hmap.congr (fun x hx => cylinderHeightMap_of_mem T ψ (hS hx))
omit [T2Space M] in
private theorem contMDiffOn_cylinderHeightMap_on
    (ψ : ℝ ≃ₘ[ℝ] ℝ) {S : Set M} (hS : S ⊆ U)
    (hψ : ∀ x ∈ S, ψ (T.inverse x).2 ∈ Ioo (0 : ℝ) 1) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (cylinderHeightMap T ψ) S := by
  have hi := T.inverse_smooth.mono hS
  have hfst := contMDiff_fst.comp_contMDiffOn hi
  have hsnd := contMDiff_snd.comp_contMDiffOn hi
  have hheight := ψ.contMDiff.comp_contMDiffOn hsnd
  have hpair := hfst.prodMk hheight
  have hmap := T.coordinate_smooth.comp hpair (fun x hx =>
    ⟨mem_univ _, hψ x hx⟩)
  exact hmap.congr (fun x hx => cylinderHeightMap_of_mem T ψ (hS hx))
include hU hC ha htail hoverlap hJ hfix hb in

theorem continuousOn_cylinderHeightMap :
    ContinuousOn (cylinderHeightMap T φ) (C ∪ U) := by
  obtain ⟨l, u, K, Q, U₀, hl, hlu, hu, hQopen, hU₀open, htailopen,
      hKcl, hQtail, hcover, hcover', hfixU₀, hfixInvU₀⟩ :=
    exists_collar_local_decomposition T hU hC side ha htail hoverlap φ hb hJ hfix
  have hφmem : ∀ x ∈ U, φ (T.inverse x).2 ∈ Ioo (0 : ℝ) 1 := by
    intro x hx
    have hz := T.inverse_mem x hx
    have hm : φ (T.inverse x).2 ∈ φ '' Ioo (0 : ℝ) 1 := ⟨_, hz.2, rfl⟩
    rw [hJ] at hm
    exact tail_subset_Ioo side ha hm
  have h0 : ContinuousOn (cylinderHeightMap T φ) U₀ :=
    continuous_id.continuousOn.congr (fun x hx => hfixU₀ x hx)
  have h1 := continuousOn_cylinderHeightMap_on T φ (S := U) Subset.rfl hφmem
  have h := h0.union_of_isOpen h1 hU₀open hU
  rw [hcover] at h
  exact h
include hU hC ha htail hoverlap hJ hfix hb in

theorem continuousOn_cylinderHeightMap_symm :
    ContinuousOn (cylinderHeightMap T φ.symm) C := by
  obtain ⟨l, u, K, Q, U₀, hl, hlu, hu, hQopen, hU₀open, htailopen,
      hKcl, hQtail, hcover, hcover', hfixU₀, hfixInvU₀⟩ :=
    exists_collar_local_decomposition T hU hC side ha htail hoverlap φ hb hJ hfix
  have hφsymm : ∀ x ∈ T.tail side a,
      φ.symm (T.inverse x).2 ∈ Ioo (0 : ℝ) 1 := by
    intro x hx
    have hh := height_mem_of_mem_tail T side ha hx
    rw [← hJ] at hh
    obtain ⟨h, hh0, hφ⟩ := hh
    have heq : φ.symm (T.inverse x).2 = h := by
      rw [← hφ, Diffeomorph.symm_apply_apply]
    rw [heq]
    exact hh0
  have h0 : ContinuousOn (cylinderHeightMap T φ.symm) U₀ :=
    continuous_id.continuousOn.congr (fun x hx => hfixInvU₀ x hx)
  have h1 := continuousOn_cylinderHeightMap_on T φ.symm
    (S := T.tail side a) (openCylinderModel_tail_subset T side ha) hφsymm
  have h := h0.union_of_isOpen h1 hU₀open htailopen
  rw [hcover'] at h
  exact h
include hU hC ha htail hoverlap hJ hfix hb in

theorem contMDiffOn_cylinderHeightMap :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (cylinderHeightMap T φ) (C ∪ U) := by
  obtain ⟨l, u, K, Q, U₀, hl, hlu, hu, hQopen, hU₀open, htailopen,
      hKcl, hQtail, hcover, hcover', hfixU₀, hfixInvU₀⟩ :=
    exists_collar_local_decomposition T hU hC side ha htail hoverlap φ hb hJ hfix
  have hφmem : ∀ x ∈ U, φ (T.inverse x).2 ∈ Ioo (0 : ℝ) 1 := by
    intro x hx
    have hz := T.inverse_mem x hx
    have hm : φ (T.inverse x).2 ∈ φ '' Ioo (0 : ℝ) 1 := ⟨_, hz.2, rfl⟩
    rw [hJ] at hm
    exact tail_subset_Ioo side ha hm
  have h0 : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (cylinderHeightMap T φ) U₀ :=
    contMDiff_id.contMDiffOn.congr (fun x hx => hfixU₀ x hx)
  have h1 := contMDiffOn_cylinderHeightMap_on T φ (S := U) Subset.rfl hφmem
  have h := h0.union_of_isOpen h1 hU₀open hU
  rw [hcover] at h
  exact h
include hU hC ha htail hoverlap hJ hfix hb in

theorem contMDiffOn_cylinderHeightMap_symm :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (cylinderHeightMap T φ.symm) C := by
  obtain ⟨l, u, K, Q, U₀, hl, hlu, hu, hQopen, hU₀open, htailopen,
      hKcl, hQtail, hcover, hcover', hfixU₀, hfixInvU₀⟩ :=
    exists_collar_local_decomposition T hU hC side ha htail hoverlap φ hb hJ hfix
  have hφsymm : ∀ x ∈ T.tail side a,
      φ.symm (T.inverse x).2 ∈ Ioo (0 : ℝ) 1 := by
    intro x hx
    have hh := height_mem_of_mem_tail T side ha hx
    rw [← hJ] at hh
    obtain ⟨h, hh0, hφ⟩ := hh
    have heq : φ.symm (T.inverse x).2 = h := by
      rw [← hφ, Diffeomorph.symm_apply_apply]
    rw [heq]
    exact hh0
  have h0 : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (cylinderHeightMap T φ.symm) U₀ :=
    contMDiff_id.contMDiffOn.congr (fun x hx => hfixInvU₀ x hx)
  have h1 := contMDiffOn_cylinderHeightMap_on T φ.symm
    (S := T.tail side a) (openCylinderModel_tail_subset T side ha) hφsymm
  have h := h0.union_of_isOpen h1 hU₀open htailopen
  rw [hcover'] at h
  exact h

noncomputable def collarShrink : OpenPartialHomeomorph M M where
  toFun := cylinderHeightMap T φ
  invFun := cylinderHeightMap T φ.symm
  source := C ∪ U
  target := C
  map_source' := by
    intro x hx
    by_cases hxU : x ∈ U
    · have hmem : cylinderHeightMap T φ x ∈ cylinderHeightMap T φ '' U :=
        mem_image_of_mem _ hxU
      rw [cylinderHeightMap_image T φ hJ] at hmem
      exact htail hmem
    · rw [cylinderHeightMap_of_not_mem T φ hxU]
      exact hx.resolve_right hxU
  map_target' := by
    intro y hy
    by_cases hyU : y ∈ U
    · right
      rw [cylinderHeightMap_of_mem T _ hyU]
      have hh := height_mem_of_mem_tail T side ha (hoverlap ⟨hy, hyU⟩)
      rw [← hJ] at hh
      obtain ⟨h, hh0, hφ⟩ := hh
      have hsymm : φ.symm (T.inverse y).2 = h := by
        rw [← hφ, Diffeomorph.symm_apply_apply]
      rw [hsymm]
      exact cylinderModel_coordinate_mem T ⟨mem_univ _, hh0⟩
    · rw [cylinderHeightMap_of_not_mem T _ hyU]
      exact Or.inl hy
  left_inv' := by
    intro x hx
    by_cases hxU : x ∈ U
    · have hz := T.inverse_mem x hxU
      rw [cylinderHeightMap_of_mem T φ hxU]
      have hmem : φ (T.inverse x).2 ∈ φ '' Ioo (0 : ℝ) 1 := ⟨_, hz.2, rfl⟩
      rw [hJ] at hmem
      have hz' : (((T.inverse x).1, φ (T.inverse x).2) : RoundCylinderSpace) ∈
          (univ : Set UnitTwoSphere) ×ˢ Ioo (0 : ℝ) 1 :=
        ⟨mem_univ _, tail_subset_Ioo side ha hmem⟩
      rw [cylinderHeightMap_coordinate T _ hz']
      change T.coordinate ((T.inverse x).1, φ.symm (φ (T.inverse x).2)) = x
      rw [Diffeomorph.symm_apply_apply]
      exact T.right_inverse hxU
    · rw [cylinderHeightMap_of_not_mem T φ hxU, cylinderHeightMap_of_not_mem T _ hxU]
  right_inv' := by
    intro y hy
    by_cases hyU : y ∈ U
    · rw [cylinderHeightMap_of_mem T _ hyU]
      have hh := height_mem_of_mem_tail T side ha (hoverlap ⟨hy, hyU⟩)
      rw [← hJ] at hh
      obtain ⟨h, hh0, hφ⟩ := hh
      have hsymm : φ.symm (T.inverse y).2 = h := by
        rw [← hφ, Diffeomorph.symm_apply_apply]
      rw [hsymm]
      have hz' : (((T.inverse y).1, h) : RoundCylinderSpace) ∈
          (univ : Set UnitTwoSphere) ×ˢ Ioo (0 : ℝ) 1 := ⟨mem_univ _, hh0⟩
      rw [cylinderHeightMap_coordinate T _ hz']
      change T.coordinate ((T.inverse y).1, φ h) = y
      rw [hφ]
      exact T.right_inverse hyU
    · rw [cylinderHeightMap_of_not_mem T _ hyU, cylinderHeightMap_of_not_mem T φ hyU]
  open_source := hC.union hU
  open_target := hC
  continuousOn_toFun :=
    continuousOn_cylinderHeightMap T hU hC side ha htail hoverlap φ hb hJ hfix
  continuousOn_invFun :=
    continuousOn_cylinderHeightMap_symm T hU hC side ha htail hoverlap φ hb hJ hfix
end HeightMap

theorem OpenCylinderModel.exists_collar_shrink
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [T2Space M]
    [IsManifold (𝓡 3) ∞ M]
    {U C : Set M} (T : OpenCylinderModel U) (hU : IsOpen U) (hC : IsOpen C)
    (side : Bool) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (htail : T.tail side a ⊆ C) (hoverlap : C ∩ U ⊆ T.tail side a) :
    ∃ Φ : OpenPartialHomeomorph M M,
      Φ.source = C ∪ U ∧ Φ.target = C ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ Φ (C ∪ U) ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ Φ.symm C ∧
      (∀ x, x ∉ U → Φ x = x) ∧
      Φ '' U = T.tail side a ∧
      ∃ φ : ℝ ≃ₘ[ℝ] ℝ, ∃ b ∈ Ioo (0 : ℝ) 1,
        φ '' Ioo 0 1 = (if side then Ioo a 1 else Ioo 0 a) ∧
        (∀ h : ℝ, (if side then b ≤ h else h ≤ b) → φ h = h) ∧
        ∀ z ∈ (univ : Set UnitTwoSphere) ×ˢ Ioo (0 : ℝ) 1,
          Φ (T.coordinate z) = T.coordinate (z.1, φ z.2) := by
  obtain ⟨φ, b, hb, hJ, hfix⟩ := exists_tail_profile side ha
  refine ⟨collarShrink T hU hC side ha htail hoverlap φ hb hJ hfix, rfl, rfl,
    contMDiffOn_cylinderHeightMap T hU hC side ha htail hoverlap φ hb hJ hfix,
    contMDiffOn_cylinderHeightMap_symm T hU hC side ha htail hoverlap φ hb hJ hfix,
    fun x hx => cylinderHeightMap_of_not_mem T φ hx,
    cylinderHeightMap_image T φ hJ, φ, b, hb, hJ, hfix,
    fun z hz => cylinderHeightMap_coordinate T φ hz⟩
end PoincareConjecture.M25.Topology3D
