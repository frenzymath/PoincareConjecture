import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FinitePLDiskAttachment
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLProperArcCut
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.PunctureBallTriangulation
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Replacement.Map

set_option autoImplicit false
open Set Geometry Topology
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

private theorem exists_returning_boundary_reparametrization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A C U W V z : Set E}
    (hA : IsFinitePLBallPair P2 A (U ∪ W))
    (hC : IsFinitePLBallPair P2 C (U ∪ V))
    (hU : IsFinitePLBallPair ℝ U z) (hUW : U ∩ W = z) (hUV : U ∩ V = z)
    (r : W ≃ₜ V) (hr : r.IsFinitePL)
    (hfix : ∀ x : W,(x : E) ∈ z → (r x : E) = x) :
    ∃ H : A ≃ₜ C,H.IsFinitePL ∧
      (∀ x : U,(H ⟨x,hA.1 (Or.inl x.property)⟩ : E) = x) ∧
      ∀ x : W,(H ⟨x,hA.1 (Or.inr x.property)⟩ : E) = r x := by
  obtain ⟨K,_,hK,hKU,_,_⟩ := hU.exists_finite_carrier_and_rim_complexes
  have hid : (Homeomorph.refl U).IsFinitePL :=
    ⟨id,⟨K,hK,hKU,K.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)⟩,fun _ => rfl⟩
  obtain ⟨b,hb,hbU,hbW⟩ := Homeomorph.exists_union_finitePL (Homeomorph.refl U) r hid hr
    (fun x => by
      change (x : E) ∈ W ↔ (x : E) ∈ V
      have h₁ : (x : E) ∈ W ↔ (x : E) ∈ z := by
        rw [←hUW]; exact (and_iff_right x.property).symm
      have h₂ : (x : E) ∈ V ↔ (x : E) ∈ z := by
        rw [←hUV]; exact (and_iff_right x.property).symm
      exact h₁.trans h₂.symm)
    (fun x hxU hxW => (hfix ⟨x,hxW⟩ (hUW.subset ⟨hxU,hxW⟩)).symm)
  obtain ⟨H,hH,hHb,_⟩ := hA.exists_extension hC b hb
  refine ⟨H,hH,?_,?_⟩
  · intro x
    exact (congrArg Subtype.val (hHb ⟨x,Or.inl x.property⟩)).trans (hbU x)
  · intro x
    exact (congrArg Subtype.val (hHb ⟨x,Or.inr x.property⟩)).trans (hbW x)

private theorem exists_nonextendable_original_replacement_branch
    {X ι E F : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (he : ∀ i j,(e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {C q W : Set E} {V : Set F} {a b : E} {c d : F}
    (hC : IsFinitePLBallPair P2 C q) (hW : IsFinitePLBallPair ℝ W {a,b})
    (hV : IsFinitePLBallPair ℝ V {c,d}) (hab : a ≠ b) (hcd : c ≠ d)
    (A U : Bool → Set E)
    (hA : ∀ i,IsFinitePLBallPair P2 (A i) (U i ∪ W))
    (hU : ∀ i,IsFinitePLBallPair ℝ (U i) {a,b})
    (hcover : A false ∪ A true = C) (hinter : A false ∩ A true = W)
    (hUq : ∀ i,U i ∪ U (!i) = q)
    (hUW : ∀ i,U i ∩ W = {a,b}) (hUV : ∀ i,U i ∩ U (!i) = {a,b})
    {f : E → X} {g : F → X}
    (hg : PolyhedralPLInCharts e g V) (hgi : InjOn g V)
    (ha : f a = g c) (hb : f b = g d)
    (k : Bool → E → X) (hk : ∀ i,PolyhedralPLInCharts e (k i) C)
    (hki : ∀ i,InjOn (k i) C) (hkeep : ∀ i,EqOn (k i) f (A i))
    (himage : ∀ i,k i '' U (!i) = g '' V)
    (hne : ¬ ∃ H : C(C,frontier R),∀ x : q,(H ⟨x,hC.1 x.property⟩ : X) = f x) :
    ∃ i : Bool,¬ ∃ H : C(C,frontier R),
      ∀ x : q,(H ⟨x,hC.1 x.property⟩ : X) = k i x := by
  classical
  obtain ⟨w,hw,hwa,hwb⟩ := hW.exists_unitInterval_chart_with_endpoints hab
  obtain ⟨v,hv,hvc,hvd⟩ := hV.exists_unitInterval_chart_with_endpoints hcd
  let r := w.symm.trans v
  have hr : r.IsFinitePL := hw.symm.trans hv
  obtain ⟨u,hu,huval⟩ := hr
  have humap : MapsTo u W V := by
    intro x hx
    rw [←huval ⟨x,hx⟩]
    exact (r ⟨x,hx⟩).property
  have hui : InjOn u W := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (r.injective (Subtype.ext
      ((huval ⟨x,hx⟩).trans (hxy.trans (huval ⟨y,hy⟩).symm))))
  have huimage : u '' W = V := by
    apply Subset.antisymm humap.image_subset
    intro y hy
    obtain ⟨x,hx⟩ := r.surjective ⟨y,hy⟩
    exact ⟨x,x.property,(huval x).symm.trans (congrArg Subtype.val hx)⟩
  have hga : (g ∘ u) a = f a := by
    have hwa' : (⟨a,hW.1 (by simp)⟩ : W) = w 0 := Subtype.ext hwa.symm
    rw [Function.comp_apply,←huval ⟨a,hW.1 (by simp)⟩,hwa']
    change g (v (w.symm (w 0))) = f a
    rw [w.symm_apply_apply]
    exact (congrArg g hvc).trans ha.symm
  have hgb : (g ∘ u) b = f b := by
    have hwb' : (⟨b,hW.1 (by simp)⟩ : W) = w 1 := Subtype.ext hwb.symm
    rw [Function.comp_apply,←huval ⟨b,hW.1 (by simp)⟩,hwb']
    change g (v (w.symm (w 1))) = f b
    rw [w.symm_apply_apply]
    exact (congrArg g hvd).trans hb.symm
  obtain ⟨J,hJ,hJs,hJu⟩ := hu
  have hgu : PolyhedralPLInCharts e (g ∘ u) W := by
    rw [←hJs]
    exact hg.comp_finitePiecewiseAffineOn J hJ ⟨J,hJ,rfl,hJu⟩
      (fun x hx => humap (hJs.subset hx))
  have hgui : InjOn (g ∘ u) W := fun x hx y hy hxy =>
    hui hx hy (hgi (humap hx) (humap hy) hxy)
  have hAC (i : Bool) : A i ⊆ C := by
    cases i
    · exact subset_union_left.trans hcover.subset
    · exact subset_union_right.trans hcover.subset
  have hUC (i : Bool) : U i ⊆ C := fun x hx => hAC i ((hA i).1 (Or.inl hx))
  have hphi (i : Bool) : ∃ phi : W ≃ₜ U (!i),phi.IsFinitePL ∧
      (∀ x : W,(g ∘ u) x = k i (phi x)) ∧
      ∀ x : W,(x : E) ∈ ({a,b} : Set E) → (phi x : E) = x := by
    obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := hU (!i)
    have hkU : PolyhedralPLInCharts e (k i) (U (!i)) :=
      hKs ▸ (hk i).restrict_finite K hK (hKs.subset.trans (hUC (!i)))
    obtain ⟨phi,hphi,hval⟩ := Dehn.Annuli.exists_original_interval_identification he
      hW (hU (!i)) hgu hkU hgui ((hki i).mono (hUC (!i))) (by
        rw [image_comp,huimage,himage i])
    refine ⟨phi,hphi,hval,?_⟩
    intro x hx
    have hxA : (x : E) ∈ A i := (hA i).1 (Or.inl ((hU i).1 hx))
    apply hki i (hUC (!i) (phi x).property) (hAC i hxA)
    rw [←hval x,hkeep i hxA]
    rcases hx with hx | hx
    · simpa only [mem_singleton_iff.mp hx] using hga
    · simpa only [mem_singleton_iff.mp hx] using hgb
  choose phi hphi hval hfix using hphi
  have hnew (i : Bool) : IsFinitePLBallPair P2 C (U i ∪ U (!i)) := (hUq i).symm ▸ hC
  choose H hH hHU hHW using fun i =>
    exists_returning_boundary_reparametrization (hA i) (hnew i) (hU i)
      (hUW i) (hUV i) (phi i) (hphi i) (hfix i)
  by_contra hn
  push Not at hn
  choose F hF using hn
  let G : C → frontier R := fun x => if hx : (x : E) ∈ A false then
    F false (H false ⟨x,hx⟩) else
    F true (H true ⟨x,(hcover.symm.subset x.property).resolve_left hx⟩)
  have hFW (i : Bool) (x : W) :
      (F i (H i ⟨x,(hA i).1 (Or.inr x.property)⟩) : X) = (g ∘ u) x := by
    have hh := hHW i x
    have hxq : (H i ⟨x,(hA i).1 (Or.inr x.property)⟩ : E) ∈ q := by
      rw [hh,←hUq i]
      exact Or.inr (phi i x).property
    exact (hF i ⟨_,hxq⟩).trans ((congrArg (k i) hh).trans (hval i x).symm)
  have hagree (x : E) (hx₀ : x ∈ A false) (hx₁ : x ∈ A true) :
      F false (H false ⟨x,hx₀⟩) = F true (H true ⟨x,hx₁⟩) := by
    have hxW := hinter.subset ⟨hx₀,hx₁⟩
    exact Subtype.ext ((hFW false ⟨x,hxW⟩).trans (hFW true ⟨x,hxW⟩).symm)
  have hG (i : Bool) (x : C) (hx : (x : E) ∈ A i) : G x = F i (H i ⟨x,hx⟩) := by
    cases i
    · simp only [G,dif_pos hx]
    · dsimp only [G]; split_ifs with hh
      · exact hagree x hh hx
      · rfl
  have hGc (i : Bool) : ContinuousOn G ((Subtype.val : C → E) ⁻¹' A i) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let p : ((Subtype.val : C → E) ⁻¹' A i) → A i := fun x => ⟨x.val.val,x.property⟩
    have hp : Continuous p := by fun_prop
    exact ((F i).continuous.comp ((H i).continuous.comp hp)).congr (fun x => (hG i x.val x.property).symm)
  have hGcont : Continuous G := by
    have hh := (hGc false).union_of_isClosed (hGc true)
      ((hA false).isCompact.isClosed.preimage continuous_subtype_val)
      ((hA true).isCompact.isClosed.preimage continuous_subtype_val)
    have hwhole : ((Subtype.val : C → E) ⁻¹' A false) ∪
        ((Subtype.val : C → E) ⁻¹' A true) = univ := by
      rw [←preimage_union,hcover]
      ext x
      simp only [mem_preimage,x.property,mem_univ]
    rw [hwhole] at hh
    exact continuousOn_univ.mp hh
  apply hne
  refine ⟨⟨G,hGcont⟩,?_⟩
  intro x
  have hxq := (hUq false).symm.subset x.property
  obtain ⟨i,hxi⟩ : ∃ i : Bool,(x : E) ∈ U i := by
    rcases hxq with hx | hx
    · exact ⟨false,hx⟩
    · exact ⟨true,hx⟩
  have hxA := (hA i).1 (Or.inl hxi)
  change (G ⟨x,hC.1 x.property⟩ : X) = f x
  rw [hG i _ hxA]
  have hh := hHU i ⟨x,hxi⟩
  have hxq' : (H i ⟨x,hxA⟩ : E) ∈ q := hh.symm ▸ x.property
  exact (hF i ⟨_,hxq'⟩).trans ((congrArg (k i) hh).trans (hkeep i hxA))

theorem exists_essential_original_returning_disk_branch
    {X ι E F : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (he : ∀ i j,(e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {C q W : Set E} {D V Z : Set F} {a b : E} {c d : F}
    (hC : IsFinitePLBallPair P2 C q)
    (hW : IsFinitePLBallPair ℝ W {a,b}) (haq : a ∈ q) (hbq : b ∈ q) (hab : a ≠ b)
    (hproperW : W \ {a,b} ⊆ C \ q)
    (hD : IsFinitePLBallPair P2 D (V ∪ Z))
    (hV : IsFinitePLBallPair ℝ V {c,d}) (hZ : IsFinitePLBallPair ℝ Z {c,d})
    (hVZ : V ∩ Z = {c,d}) (hcd : c ≠ d)
    {f : E → X} {g : F → X}
    (hf : PolyhedralPLInCharts e f C) (hg : PolyhedralPLInCharts e g D)
    (hfi : InjOn f C) (hgi : InjOn g D)
    (hfR : MapsTo f C R) (hgR : MapsTo g D R)
    (hfproper : ∀ x ∈ C,f x ∈ frontier R ↔ x ∈ q)
    (hgproper : ∀ x ∈ D,g x ∈ frontier R ↔ x ∈ V)
    (himage : f '' W = g '' Z) (ha : f a = g c) (hb : f b = g d)
    (htrace : D ∩ g ⁻¹' (f '' C) = Z)
    (hne : ¬ ∃ H : C(C,frontier R),∀ x : q,(H ⟨x,hC.1 x.property⟩ : X) = f x) :
    ∃ (A B U T : Set E) (k : E → X),
      IsFinitePLBallPair P2 A (U ∪ W) ∧ IsFinitePLBallPair P2 B (T ∪ W) ∧
      IsFinitePLBallPair ℝ U {a,b} ∧ IsFinitePLBallPair ℝ T {a,b} ∧
      A ∪ B = C ∧ A ∩ B = W ∧ U ∪ T = q ∧ U ∩ T = {a,b} ∧
      A ∩ q = U ∧ B ∩ q = T ∧
      PolyhedralPLInCharts e k C ∧ InjOn k C ∧ IsEmbedding (fun x : C => k x) ∧
      MapsTo k C R ∧ EqOn k f A ∧ k '' B = g '' D ∧ k '' T = g '' V ∧
      k '' C = (f '' A) ∪ (g '' D) ∧
      (∀ x ∈ C,k x ∈ frontier R ↔ x ∈ q) ∧
      ¬ ∃ H : C(C,frontier R),∀ x : q,(H ⟨x,hC.1 x.property⟩ : X) = k x := by
  classical
  obtain ⟨U₀,U₁,hU₀,hU₁,hUq₀,hUi₀⟩ := hC.exists_boundary_arcs haq hbq hab
  obtain ⟨A₀,A₁,hA₀,hA₁,hAC₀,hAi₀,hAq₀,hAq₁⟩ :=
    hC.exists_proper_arc_cut hU₀ hU₁ hW hab hUi₀.subset hUq₀ hproperW
  let A : Bool → Set E := fun i => if i then A₁ else A₀
  let U : Bool → Set E := fun i => if i then U₁ else U₀
  have hA (i : Bool) : IsFinitePLBallPair P2 (A i) (U i ∪ W) := by
    cases i
    · exact hA₀
    · simpa only [A,U,if_true,union_comm] using hA₁
  have hU (i : Bool) : IsFinitePLBallPair ℝ (U i) {a,b} := by cases i <;> assumption
  have hAC : A false ∪ A true = C := hAC₀
  have hAi : A false ∩ A true = W := hAi₀
  have hAC' (i : Bool) : A i ∪ A (!i) = C := by
    cases i
    · exact hAC
    · exact (union_comm _ _).trans hAC
  have hAi' (i : Bool) : A i ∩ A (!i) = W := by
    cases i
    · exact hAi
    · exact (inter_comm _ _).trans hAi
  have hUq (i : Bool) : U i ∪ U (!i) = q := by
    cases i
    · exact hUq₀
    · exact (union_comm _ _).trans hUq₀
  have hUV (i : Bool) : U i ∩ U (!i) = {a,b} := by
    cases i
    · exact hUi₀
    · exact (inter_comm _ _).trans hUi₀
  have hAq (i : Bool) : A i ∩ q = U i := by cases i <;> assumption
  have hAsub (i : Bool) : A i ⊆ C := subset_union_left.trans (hAC' i).subset
  have hUsub (i : Bool) : U i ⊆ A i := fun _ hx => (hA i).1 (Or.inl hx)
  have hUW (i : Bool) : U i ∩ W = {a,b} := by
    apply Subset.antisymm
    · intro x hx
      by_contra hn
      exact (hproperW ⟨hx.2,hn⟩).2 ((hAq i).symm.subset hx.1).2
    · exact fun x hx => ⟨(hU i).1 hx,hW.1 hx⟩
  have hCcopy := hC
  obtain ⟨_,_,_,_,_,_,⟨_,⟨J,hJ,hJs,_⟩,_⟩,_⟩ := hCcopy
  have hsource (i : Bool) : ∃ O : SimplicialComplex ℝ E,O.faces.Finite ∧ O.space = A i := by
    obtain ⟨_,_,_,_,_,_,⟨_,⟨O,hO,hOs,_⟩,_⟩,_⟩ := hA i
    exact ⟨O,hO,hOs⟩
  choose O hO hOs using hsource
  have hmaps (i : Bool) : ∃ k : E → X,PolyhedralPLInCharts e k C ∧ InjOn k C ∧
      IsEmbedding (fun x : C => k x) ∧ EqOn k f (A i) ∧
      k '' A (!i) = g '' D ∧ k '' U (!i) = g '' V ∧ k '' C = f '' A i ∪ g '' D := by
    have hc : A (!i) ∪ (O i).space = J.space := by
      rw [hOs,hJs,union_comm,hAC' i]
    have hi : A (!i) ∩ (O i).space = W := by
      rw [hOs,inter_comm,hAi' i]
    obtain ⟨k,hk,hki,hke,hkeep,hkD,hkU,hkimage⟩ :=
      Dehn.Annuli.exists_original_returning_disk_replacement he J (O i) hJ (hO i)
        (hA (!i)) hD (hU (!i)) hW hV hZ (hUW (!i)) hVZ hab hcd hc hi
        (hJs.symm ▸ hf) hg (hJs.symm ▸ hfi) hgi himage ha hb (by simpa only [hJs] using htrace)
    exact ⟨k,hJs ▸ hk,hJs ▸ hki,hJs ▸ hke,hOs i ▸ hkeep,hkD,hkU,
      by simpa only [hJs,hOs] using hkimage⟩
  choose k hk hki hke hkeep hkD hkU hkimage using hmaps
  have hgV : PolyhedralPLInCharts e g V := by
    obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := hV
    exact hKs ▸ hg.restrict_finite K hK (fun x hx => hD.1 (Or.inl (hKs.subset hx)))
  obtain ⟨i,hine⟩ := exists_nonextendable_original_replacement_branch he hC hW hV hab hcd
    A U hA hU hAC hAi hUq hUW hUV hgV (hgi.mono (fun _ hx => hD.1 (Or.inl hx)))
      ha hb k hk hki hkeep hkU hne
  have hfrontimage : (k i '' C) ∩ frontier R = k i '' q := by
    have hAiFront : (f '' A i) ∩ frontier R = f '' U i := by
      ext y
      constructor
      · rintro ⟨⟨x,hx,rfl⟩,hy⟩
        exact ⟨x,(hAq i).subset ⟨hx,(hfproper x (hAsub i hx)).mp hy⟩,rfl⟩
      · rintro ⟨x,hx,rfl⟩
        have hh := (hAq i).symm.subset hx
        exact ⟨⟨x,hh.1,rfl⟩,(hfproper x (hAsub i hh.1)).mpr hh.2⟩
    have hDFront : (g '' D) ∩ frontier R = g '' V := by
      ext y
      constructor
      · rintro ⟨⟨x,hx,rfl⟩,hy⟩
        exact ⟨x,(hgproper x hx).mp hy,rfl⟩
      · rintro ⟨x,hx,rfl⟩
        exact ⟨⟨x,hD.1 (Or.inl hx),rfl⟩,(hgproper x (hD.1 (Or.inl hx))).mpr hx⟩
    rw [hkimage,union_inter_distrib_right,hAiFront,hDFront,←hUq i,image_union,
      image_congr ((hkeep i).mono (hUsub i)),hkU]
  have hkproper (x : E) (hx : x ∈ C) : k i x ∈ frontier R ↔ x ∈ q := by
    constructor
    · intro hfront
      obtain ⟨y,hy,hyx⟩ := hfrontimage.subset ⟨⟨x,hx,rfl⟩,hfront⟩
      exact hki i (hC.1 hy) hx hyx ▸ hy
    · intro hxq
      exact (hfrontimage.symm.subset ⟨x,hxq,rfl⟩).2
  refine ⟨A i,A (!i),U i,U (!i),k i,hA i,hA (!i),hU i,hU (!i),hAC' i,hAi' i,
    hUq i,hUV i,hAq i,hAq (!i),hk i,hki i,hke i,?_,hkeep i,hkD i,hkU i,hkimage i,
    hkproper,hine⟩
  intro x hx
  rcases (hkimage i).subset ⟨x,hx,rfl⟩ with ⟨y,hy,hyx⟩ | ⟨y,hy,hyx⟩
  · exact hyx ▸ hfR (hAsub i hy)
  · exact hyx ▸ hgR hy

end PoincareConjecture.M76
