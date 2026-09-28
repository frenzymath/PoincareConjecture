import PoincareConjecture.Proofs.M76.Horizon.Dehn.Collars.InwardCompression









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.Dehn
local notation "I" => Icc (0 : ℝ) 1

theorem exists_inward_collar_compression_homotopy
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (K : SimplicialComplex ℝ F) (L : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hL : L.faces.Finite)
    (c : E × ℝ → F) (hc : FinitePiecewiseAffineOn c (L.space ×ˢ I))
    (hinj : InjOn c (L.space ×ˢ I)) (hinside : MapsTo c (L.space ×ˢ I) K.space)
    (hopen : IsOpen ((Subtype.val : K.space → F) ⁻¹'
      (c '' (L.space ×ˢ Ico (0 : ℝ) 1)))) :
    ∃ (D : Set F) (H : K.space ≃ₜ D), H.IsFinitePL ∧ D ⊆ K.space ∧
      (∀ z ∈ L.space ×ˢ I,c z ∈ D ↔ (1/2 : ℝ) ≤ z.2) ∧
      ∃ G : C(I × K.space,K.space),
        (∀ x,G (0,x)=x) ∧ (∀ x,(G (1,x) : F)=H x) ∧
        (∀ (t : I) z (hz : z ∈ L.space ×ˢ I),
          (G (t,⟨c z,hinside hz⟩) : F)=c (z.1,z.2+(t : ℝ)*(1-z.2)/2)) ∧
        (∀ (t : I) (x : K.space),
          (x : F) ∉ c '' (L.space ×ˢ Ico (0 : ℝ) 1) → G (t,x)=x) ∧
        ∀ (T : Set F) (B : Set E),
          (∀ z ∈ L.space ×ˢ I,c z ∈ T ↔ z.1 ∈ B) →
          ∀ (t : I) (x : K.space),(G (t,x) : F) ∈ T ↔ (x : F) ∈ T := by
  classical
  obtain ⟨D,H,hH,hDK,hHval,hHfix,hclear⟩ :=
    exists_inward_collar_compression K L hK hL c hc hinj hinside hopen
  obtain ⟨J,hJ,hJs,hcover,hroof⟩ :=
    exists_finite_collar_strip_residual K L hK hL c hc hinj hinside hopen
  obtain ⟨C,hC,hCval⟩ := hc.exists_homeomorph_image hinj
  obtain ⟨r,hr,hrval⟩ := hC.symm
  have hrleft (z : E × ℝ) (hz : z ∈ L.space ×ˢ I) : r (c z)=z := by
    have hh := hrval (C ⟨z,hz⟩)
    rw [C.symm_apply_apply,hCval] at hh
    exact hh.symm
  have hrright (x : F) (hx : x ∈ c '' (L.space ×ˢ I)) : c (r x)=x := by
    obtain ⟨z,hz,rfl⟩ := hx
    rw [hrleft z hz]
  have hrmem (x : F) (hx : x ∈ c '' (L.space ×ˢ I)) : r x ∈ L.space ×ˢ I := by
    obtain ⟨z,hz,rfl⟩ := hx
    rwa [hrleft z hz]
  let step (t : I) (z : E × ℝ) : E × ℝ := (z.1,z.2+(t : ℝ)*(1-z.2)/2)
  have hstep (t : I) {z : E × ℝ} (hz : z ∈ L.space ×ˢ I) : step t z ∈ L.space ×ˢ I := by
    refine ⟨hz.1,?_,?_⟩ <;> dsimp [step]
    · have hprod : 0 ≤ (t : ℝ)*(1-z.2) := mul_nonneg t.property.1 (sub_nonneg.mpr hz.2.2)
      linarith [hz.2.1]
    · have hprod : (t : ℝ)*(1-z.2) ≤ 1-z.2 :=
        mul_le_of_le_one_left (sub_nonneg.mpr hz.2.2) t.property.2
      linarith [hz.2.2]
  let A : Set (I × K.space) := {z | (z.2 : F) ∈ c '' (L.space ×ˢ I)}
  let B : Set (I × K.space) := {z | (z.2 : F) ∈ J.space}
  let g : I × K.space → F := fun z =>
    if (z.2 : F) ∈ c '' (L.space ×ˢ I) then c (step z.1 (r z.2)) else z.2
  have hgA (z : I × K.space) (hz : z ∈ A) : g z = c (step z.1 (r z.2)) :=
    if_pos hz
  have hgB (z : I × K.space) (hz : z ∈ B) : g z = z.2 := by
    by_cases hx : (z.2 : F) ∈ c '' (L.space ×ˢ I)
    · obtain ⟨w,hw,hweq⟩ := hx
      have hw1 : w.2=1 := (hroof w hw).mp (hweq.symm ▸ hz)
      have hzA : z ∈ A := by
        change (z.2 : F) ∈ c '' (L.space ×ˢ I)
        exact ⟨w,hw,hweq⟩
      rw [hgA z hzA,←hweq,hrleft w hw]
      have hs : step z.1 w=w := by ext <;> simp [step,hw1]
      rw [hs]
    · exact if_neg hx
  have hgmem (z : I × K.space) : g z ∈ K.space := by
    by_cases hz : z ∈ A
    · rw [hgA z hz]
      exact hinside (hstep z.1 (hrmem z.2 hz))
    · change (if (z.2 : F) ∈ c '' (L.space ×ˢ I) then _ else _) ∈ _
      change (z.2 : F) ∉ c '' (L.space ×ˢ I) at hz
      rw [if_neg hz]
      exact z.2.property
  have hAc : IsClosed A :=
    (((L.isCompact_space_of_finite hL).prod isCompact_Icc).image_of_continuousOn
      hc.continuousOn).isClosed.preimage (continuous_subtype_val.comp continuous_snd)
  have hBc : IsClosed B := (J.isCompact_space_of_finite hJ).isClosed.preimage
    (continuous_subtype_val.comp continuous_snd)
  have hAB : A ∪ B = univ := by
    apply eq_univ_of_forall
    intro z
    exact hcover.symm.subset z.2.property
  have hgcA : ContinuousOn g A := by
    have hrc : ContinuousOn (fun z : I × K.space => r z.2) A :=
      hr.continuousOn.comp (continuous_subtype_val.comp continuous_snd).continuousOn (fun _ hz => hz)
    have hsc : ContinuousOn (fun z : I × K.space => step z.1 (r z.2)) A :=
      hrc.fst.prodMk (hrc.snd.add
        (((continuous_subtype_val.comp continuous_fst).continuousOn.mul
          (continuousOn_const.sub hrc.snd)).div_const 2))
    exact (hc.continuousOn.comp hsc (fun z hz => hstep z.1 (hrmem z.2 hz))).congr
      (fun z hz => hgA z hz)
  have hgcB : ContinuousOn g B :=
    (continuous_subtype_val.comp continuous_snd).continuousOn.congr (fun z hz => hgB z hz)
  have hgc : Continuous g := continuousOn_univ.mp (hAB ▸ hgcA.union_of_isClosed hgcB hAc hBc)
  let G : C(I × K.space,K.space) := ⟨fun z => ⟨g z,hgmem z⟩,hgc.subtype_mk _⟩
  have hGval (t : I) (z : E × ℝ) (hz : z ∈ L.space ×ˢ I) :
      (G (t,⟨c z,hinside hz⟩) : F)=c (step t z) := by
    change g (t,⟨c z,hinside hz⟩)=_
    rw [hgA _ (mem_image_of_mem c hz),hrleft z hz]
  have hGfix (t : I) (x : K.space)
      (hx : (x : F) ∉ c '' (L.space ×ˢ Ico (0 : ℝ) 1)) : G (t,x)=x := by
    apply Subtype.ext
    exact hgB _ (hJs.symm.subset ⟨x.property,hx⟩)
  refine ⟨D,H,hH,hDK,hclear,G,?_,?_,hGval,hGfix,?_⟩
  · intro x
    apply Subtype.ext
    by_cases hx : (x : F) ∈ c '' (L.space ×ˢ I)
    · obtain ⟨z,hz,hzx⟩ := hx
      have hx' : x=⟨c z,hinside hz⟩ := Subtype.ext hzx.symm
      rw [hx',hGval 0 z hz]
      simp [step]
    · have hx' : (x : F) ∉ c '' (L.space ×ˢ Ico (0 : ℝ) 1) :=
        fun hh => hx ((image_mono (prod_mono_right Ico_subset_Icc_self)) hh)
      exact congrArg Subtype.val (hGfix 0 x hx')
  · intro x
    by_cases hx : (x : F) ∈ c '' (L.space ×ˢ I)
    · obtain ⟨z,hz,hzx⟩ := hx
      have hx' : x=⟨c z,hinside hz⟩ := Subtype.ext hzx.symm
      rw [hx',hGval 1 z hz,hHval z hz]
      congr 1
      ext <;> simp [step] <;> ring
    · have hx' : (x : F) ∉ c '' (L.space ×ˢ Ico (0 : ℝ) 1) :=
        fun hh => hx ((image_mono (prod_mono_right Ico_subset_Icc_self)) hh)
      rw [hGfix 1 x hx',hHfix x hx']
  · intro T B hmark t x
    by_cases hx : (x : F) ∈ c '' (L.space ×ˢ I)
    · obtain ⟨z,hz,hzx⟩ := hx
      have hx' : x=⟨c z,hinside hz⟩ := Subtype.ext hzx.symm
      rw [hx',hGval t z hz,hmark _ (hstep t hz),hmark z hz]
    · have hx' : (x : F) ∉ c '' (L.space ×ˢ Ico (0 : ℝ) 1) :=
        fun hh => hx ((image_mono (prod_mono_right Ico_subset_Icc_self)) hh)
      rw [hGfix t x hx']

end PoincareConjecture.M76.Dehn

