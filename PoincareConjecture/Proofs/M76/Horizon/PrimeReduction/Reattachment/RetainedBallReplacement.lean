import PoincareConjecture.Proofs.M76.Mathlib.UnitBallPairs
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.SphereModelCap

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

private theorem exists_continuous_union_map
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s u : Set X} {t v : Set Y} (hs : IsClosed s) (hu : IsClosed u)
    (e : C(s,t)) (f : C(u,v))
    (hagree : ∀ (x : X) (hxs : x ∈ s) (hxu : x ∈ u),
      (e ⟨x,hxs⟩ : Y) = f ⟨x,hxu⟩) :
    ∃ F : C((s ∪ u : Set X), (t ∪ v : Set Y)),
      (∀ x : s, (F ⟨x,Or.inl x.property⟩ : Y) = e x) ∧
      (∀ x : u, (F ⟨x,Or.inr x.property⟩ : Y) = f x) := by
  classical
  let F : (s ∪ u : Set X) → (t ∪ v : Set Y) := fun x =>
    if hx : (x : X) ∈ s then ⟨e ⟨x,hx⟩,Or.inl (e ⟨x,hx⟩).property⟩
    else ⟨f ⟨x,x.property.resolve_left hx⟩,Or.inr (f ⟨x,x.property.resolve_left hx⟩).property⟩
  have hFs (x : s) : F ⟨x,Or.inl x.property⟩ = ⟨e x,Or.inl (e x).property⟩ := by
    simp only [F,dif_pos x.property]
  have hFu (x : u) : F ⟨x,Or.inr x.property⟩ = ⟨f x,Or.inr (f x).property⟩ := by
    by_cases hx : (x : X) ∈ s
    · apply Subtype.ext
      simpa only [F,dif_pos hx] using hagree x hx x.property
    · simp only [F,dif_neg hx]
  let S : Set (s ∪ u : Set X) := {x | (x : X) ∈ s}
  let U : Set (s ∪ u : Set X) := {x | (x : X) ∈ u}
  have hcS : ContinuousOn F S := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous (fun x : S =>
        (⟨e ⟨x.val.val,x.property⟩,Or.inl (e ⟨x.val.val,x.property⟩).property⟩ :
          (t ∪ v : Set Y))) := by fun_prop
    convert hc using 1
    funext x
    exact hFs ⟨x.val.val,x.property⟩
  have hcU : ContinuousOn F U := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous (fun x : U =>
        (⟨f ⟨x.val.val,x.property⟩,Or.inr (f ⟨x.val.val,x.property⟩).property⟩ :
          (t ∪ v : Set Y))) := by fun_prop
    convert hc using 1
    funext x
    exact hFu ⟨x.val.val,x.property⟩
  have hcover : S ∪ U = univ := eq_univ_of_forall fun x => x.property
  have hcont := hcS.union_of_isClosed hcU
    (hs.preimage continuous_subtype_val) (hu.preimage continuous_subtype_val)
  rw [hcover] at hcont
  exact ⟨⟨F,continuousOn_univ.mp hcont⟩,
    fun x => congrArg Subtype.val (hFs x),fun x => congrArg Subtype.val (hFu x)⟩

theorem exists_closed_union_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s u : Set X} {t v : Set Y}
    (hs : IsClosed s) (hu : IsClosed u) (ht : IsClosed t) (hv : IsClosed v)
    (e : s ≃ₜ t) (f : u ≃ₜ v)
    (hoverlap : ∀ x : s, (x : X) ∈ u ↔ (e x : Y) ∈ v)
    (hagree : ∀ (x : X) (hxs : x ∈ s) (hxu : x ∈ u),
      (e ⟨x,hxs⟩ : Y) = f ⟨x,hxu⟩) :
    ∃ H : (s ∪ u : Set X) ≃ₜ (t ∪ v : Set Y),
      (∀ x : s, (H ⟨x,Or.inl x.property⟩ : Y) = e x) ∧
      (∀ x : u, (H ⟨x,Or.inr x.property⟩ : Y) = f x) := by
  obtain ⟨F,hFs,hFu⟩ := exists_continuous_union_map hs hu
    ⟨e,e.continuous⟩ ⟨f,f.continuous⟩ hagree
  have hagree' (y : Y) (hyt : y ∈ t) (hyv : y ∈ v) :
      (e.symm ⟨y,hyt⟩ : X) = f.symm ⟨y,hyv⟩ := by
    have hxu : (e.symm ⟨y,hyt⟩ : X) ∈ u :=
      (hoverlap _).mpr (by simpa only [e.apply_symm_apply] using hyv)
    have heq : f ⟨e.symm ⟨y,hyt⟩,hxu⟩ = ⟨y,hyv⟩ := by
      apply Subtype.ext
      rw [← hagree _ (e.symm ⟨y,hyt⟩).property hxu]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨y,hyt⟩)
    exact congrArg Subtype.val (f.injective (heq.trans (f.apply_symm_apply _).symm))
  obtain ⟨G,hGt,hGv⟩ := exists_continuous_union_map ht hv
    ⟨e.symm,e.symm.continuous⟩ ⟨f.symm,f.symm.continuous⟩ hagree'
  have hGF : Function.LeftInverse G F := by
    intro x
    apply Subtype.ext
    rcases x.property with hx | hx
    · have hFx : F x = ⟨e ⟨x,hx⟩,Or.inl (e ⟨x,hx⟩).property⟩ :=
        Subtype.ext (hFs ⟨x,hx⟩)
      rw [hFx,hGt]
      exact congrArg Subtype.val (e.symm_apply_apply ⟨x,hx⟩)
    · have hFx : F x = ⟨f ⟨x,hx⟩,Or.inr (f ⟨x,hx⟩).property⟩ :=
        Subtype.ext (hFu ⟨x,hx⟩)
      rw [hFx,hGv]
      exact congrArg Subtype.val (f.symm_apply_apply ⟨x,hx⟩)
  have hFG : Function.RightInverse G F := by
    intro y
    apply Subtype.ext
    rcases y.property with hy | hy
    · have hGy : G y = ⟨e.symm ⟨y,hy⟩,Or.inl (e.symm ⟨y,hy⟩).property⟩ :=
        Subtype.ext (hGt ⟨y,hy⟩)
      rw [hGy,hFs]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨y,hy⟩)
    · have hGy : G y = ⟨f.symm ⟨y,hy⟩,Or.inr (f.symm ⟨y,hy⟩).property⟩ :=
        Subtype.ext (hGv ⟨y,hy⟩)
      rw [hGy,hFu]
      exact congrArg Subtype.val (f.apply_symm_apply ⟨y,hy⟩)
  exact ⟨{
    toFun := F
    invFun := G
    left_inv := hGF
    right_inv := hFG
    continuous_toFun := F.continuous
    continuous_invFun := G.continuous },hFs,hFu⟩

local notation "V3" => (Fin 3 → ℝ)

theorem exists_retained_ball_replacement
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A Q S : Set X} {A' C T : Set Y}
    (hA : IsClosed A) (hQ : IsClosed Q) (hA' : IsClosed A') (hC : IsClosed C)
    (hball : IsUnitBallPair V3 Q S) (hcap : IsUnitBallPair V3 C T)
    (hSQ : A ∩ Q = S) (hTC : A' ∩ C = T) (H : A ≃ₜ A')
    (hmark : ∀ x : A, (x : X) ∈ S ↔ (H x : Y) ∈ T) :
    ∃ G : (A ∪ Q : Set X) ≃ₜ (A' ∪ C : Set Y),
      (∀ x : A, (G ⟨x,Or.inl x.property⟩ : Y) = H x) ∧
      (∀ x : (A ∪ Q : Set X), (x : X) ∈ Q ↔ (G x : Y) ∈ C) ∧
      (∀ y : A', (G.symm ⟨y,Or.inl y.property⟩ : X) = H.symm y) := by
  have hSA : S ⊆ A := hSQ.symm.subset.trans inter_subset_left
  have hTA : T ⊆ A' := hTC.symm.subset.trans inter_subset_left
  let HB : S ≃ₜ T := H.restrictSubsets hSA hTA hmark
  obtain ⟨F,hF,hFmark⟩ := hball.exists_extension hcap HB
  have hoverlap (x : A) : (x : X) ∈ Q ↔ (H x : Y) ∈ C := by
    calc
      _ ↔ (x : X) ∈ S := by rw [← hSQ]; exact (and_iff_right x.property).symm
      _ ↔ (H x : Y) ∈ T := hmark x
      _ ↔ (H x : Y) ∈ C := by rw [← hTC]; exact and_iff_right (H x).property
  have hagree (x : X) (hxA : x ∈ A) (hxQ : x ∈ Q) :
      (H ⟨x,hxA⟩ : Y) = F ⟨x,hxQ⟩ := by
    have hxS : x ∈ S := hSQ.subset ⟨hxA,hxQ⟩
    exact (congrArg Subtype.val (hF ⟨x,hxS⟩)).symm
  obtain ⟨G,hGA,hGQ⟩ := exists_closed_union_homeomorph hA hQ hA' hC H F hoverlap hagree
  refine ⟨G,hGA,?_,?_⟩
  · intro x
    rcases x.property with hxA | hxQ
    · rw [hGA ⟨x,hxA⟩]
      exact hoverlap ⟨x,hxA⟩
    · have hxC : (G x : Y) ∈ C := by
        rw [hGQ ⟨x,hxQ⟩]
        exact (F ⟨x,hxQ⟩).property
      exact iff_of_true hxQ hxC
  · intro y
    have hg : G ⟨H.symm y,Or.inl (H.symm y).property⟩ = ⟨y,Or.inl y.property⟩ := by
      apply Subtype.ext
      rw [hGA]
      exact congrArg Subtype.val (H.apply_symm_apply y)
    exact congrArg Subtype.val (G.injective ((G.apply_symm_apply _).trans hg.symm))

theorem ChartwisePLSphere.exists_retained_cone_replacement
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {A Q S : Set X}
    (s : ChartwisePLSphere e S) (hA : IsCompact A) (hQ : IsClosed Q)
    (hball : IsUnitBallPair V3 Q S) (hcontact : A ∩ Q = S)
    (phi : X → E) (hphi : Continuous phi) (hinj : InjOn phi A)
    (hPL : ∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target) :
    let j : X → E × ℝ := fun x => (phi x,0)
    let C := convexJoin ℝ {((0 : E), (1 : ℝ))} (j '' S)
    IsFinitePLBallPair V3 C (j '' S) ∧
      ∃ G : (A ∪ Q : Set X) ≃ₜ (j '' A ∪ C : Set (E × ℝ)),
        (∀ x : A, (G ⟨x,Or.inl x.property⟩ : E × ℝ) = j x) ∧
        (∀ x : (A ∪ Q : Set X), (x : X) ∈ Q ↔ (G x : E × ℝ) ∈ C) := by
  classical
  let j : X → E × ℝ := fun x => (phi x,0)
  let C := convexJoin ℝ {((0 : E), (1 : ℝ))} (j '' S)
  have hSA : S ⊆ A := hcontact.symm.subset.trans inter_subset_left
  have hj : Continuous j := hphi.prodMk continuous_const
  have hji : InjOn j A := fun x hx y hy hxy => hinj hx hy (congrArg Prod.fst hxy)
  have hcap : IsFinitePLBallPair V3 C (j '' S) := by
    simpa only [C,j,image_image,Function.comp_def] using
      s.isFinitePLBallPair_model_cap phi hPL (hinj.mono hSA) rfl
  obtain ⟨HB,_,hHB⟩ := hcap.exists_cube_chart (ContinuousLinearEquiv.refl ℝ V3)
  have hcapTop : IsUnitBallPair V3 C (j '' S) :=
    ⟨hcap.1,HB,by simpa only [frontier_closedBall _ one_ne_zero] using hHB⟩
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA
  let H : A ≃ₜ j '' A := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn j A hji) (hj.comp continuous_subtype_val |>.subtype_mk _)
  have hHval (x : A) : (H x : E × ℝ) = j x := rfl
  have hconeContact : (j '' A) ∩ C = j '' S := by
    apply Subset.antisymm
    · rintro z ⟨⟨y,hy,rfl⟩,hz⟩
      obtain ⟨p,hp,b,⟨x,hx,rfl⟩,a,d,ha,hd,had,heq⟩ := mem_convexJoin.mp hz
      have hp' : p = ((0 : E), (1 : ℝ)) := hp
      subst p
      have ha0 : a = 0 := by
        have hh := congrArg Prod.snd heq
        change a * 1 + d * 0 = 0 at hh
        simpa only [mul_one,mul_zero,add_zero] using hh
      have hd1 : d = 1 := by linarith
      have hxy : j x = j y := by simpa only [ha0,hd1,zero_smul,one_smul,zero_add] using heq
      exact ⟨x,hx,hxy⟩
    · intro z hz
      exact ⟨image_mono hSA hz,hcap.1 hz⟩
  have hmark (x : A) : (x : X) ∈ S ↔ (H x : E × ℝ) ∈ j '' S := by
    rw [hHval]
    constructor
    · exact mem_image_of_mem j
    · rintro ⟨y,hy,heq⟩
      exact hji (hSA hy) x.property heq ▸ hy
  obtain ⟨G,hGA,hGQ,_⟩ := exists_retained_ball_replacement hA.isClosed hQ
    (hA.image hj).isClosed hcap.isCompact.isClosed hball hcapTop hcontact hconeContact H hmark
  exact ⟨hcap,G,fun x => (hGA x).trans (hHval x),hGQ⟩

end PoincareConjecture.M76
