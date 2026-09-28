import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcTubeBranchInverse
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Mathlib.OriginalStripDoubleLocus

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "C3" => (P2 × ℝ)

theorem originalStripSheet_finitePL (i : Bool) :
    FinitePiecewiseAffineOn (originalStripSheet i) source := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJs, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).prod
      (isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num))
  let x := (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
  let y := (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  let a := (y.prod (if i then -y else y)).prod x
  have ha : (a : P2 → C3) = originalStripSheet i := by
    funext p
    cases i <;> rfl
  rw [← ha]
  exact ⟨J, hJ, hJs, J.affineOnFaces_affine a⟩

theorem exists_original_tube_source_strips
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    (C : Set X) (K : SimplicialComplex ℝ E)
    (F : X → E) (H : C ≃ₜ K.space) (g : E → C)
    (hH : ∀ x : C, (H x : E) = F x)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hsep : ∀ x ∈ C, ∀ y : X, F x = F y → x = y)
    (P T : Fin 2 → SimplicialComplex ℝ V2)
    (M : Fin 2 → SimplicialComplex ℝ E) (f : V2 → X)
    (hinj : ∀ i, InjOn f (P i).space)
    (hclip : ∀ i, (T i).space = (P i).space ∩ f ⁻¹' C)
    (hPL : ∀ i, FinitePiecewiseAffineOn (F ∘ f) (T i).space)
    (himage : ∀ i, (F ∘ f) '' (T i).space = (M i).space)
    (hMK : ∀ i, M i ≤ K)
    {D : Set V2} (hPD : ∀ i, (P i).space ⊆ D)
    (hdisj : Disjoint (P 0).space (P 1).space)
    (hconfine : D ∩ f ⁻¹' C ⊆ (P 0).space ∪ (P 1).space)
    (tau : C3 → E) (htauPL : FinitePiecewiseAffineOn tau tube)
    (htaui : InjOn tau tube) (htauK : MapsTo tau tube K.space)
    (hsheet : ∀ i z, z ∈ tube →
      (tau z ∈ (M i).space ↔ z.1.2 = if i = 0 then z.1.1 else -z.1.1)) :
    ∃ c : Bool → P2 → V2,
      (∀ i, FinitePiecewiseAffineOn (c i) source ∧ InjOn (c i) source ∧
        MapsTo (c i) source (P (if i then 1 else 0)).space) ∧
      Disjoint (c false '' source) (c true '' source) ∧
      (∀ i p, p ∈ source → f (c i p) = (g (tau (originalStripSheet i p)) : X)) ∧
      InjOn (fun z => (g (tau z) : X)) tube ∧
      D ∩ f ⁻¹' ((fun z => (g (tau z) : X)) '' tube) =
        (c false '' source) ∪ (c true '' source) := by
  classical
  obtain ⟨u, hu, hvalue, hFvalue, hforward, hunique⟩ :=
    exists_original_signed_tube_branch_inverses C K F H g hH hg hsep P T M
      (fun _ => f) hinj hclip hPL himage hMK
  choose v hv hvvalue using fun i => (hu i).1
  let index : Bool → Fin 2 := fun i => if i then 1 else 0
  have hdiag (i : Bool) (p : P2) (hp : p ∈ source) :
      tau (originalStripSheet i p) ∈ (M (index i)).space := by
    apply (hsheet (index i) _ (originalStripSheet_mem_tube i hp)).mpr
    cases i <;> simp [index, originalStripSheet]
  let c : Bool → P2 → V2 := fun i => v (index i) ∘ tau ∘ originalStripSheet i
  have hcv (i : Bool) (p : P2) (hp : p ∈ source) :
      c i p = (u (index i) ⟨tau (originalStripSheet i p), hdiag i p hp⟩ : V2) :=
    (hvvalue (index i) ⟨tau (originalStripSheet i p), hdiag i p hp⟩).symm
  have hcP (i : Bool) : MapsTo (c i) source (P (index i)).space := by
    intro p hp
    rw [hcv i p hp]
    exact ((hclip _).subset (u _ _).property).1
  have hcvalue (i : Bool) (p : P2) (hp : p ∈ source) :
      f (c i p) = (g (tau (originalStripSheet i p)) : X) := by
    rw [hcv i p hp]
    exact hvalue _ _
  have hFg (z : E) (hz : z ∈ K.space) : F (g z) = z := by
    rw [← hH (g z)]
    have he : g z = H.symm ⟨z, hz⟩ := Subtype.ext (hg ⟨z, hz⟩)
    rw [he, H.apply_symm_apply]
  have hgi : InjOn (fun z => (g (tau z) : X)) tube := by
    intro z hz w hw he
    apply htaui hz hw
    have hh := congrArg F he
    simpa only [hFg _ (htauK hz), hFg _ (htauK hw)] using hh
  have hci (i : Bool) : InjOn (c i) source := by
    intro p hp q hq he
    have hh := congrArg f he
    rw [hcvalue i p hp, hcvalue i q hq] at hh
    have hd := hgi (originalStripSheet_mem_tube i hp)
      (originalStripSheet_mem_tube i hq) hh
    exact congrArg (fun z : C3 => (z.2, z.1.1)) hd
  refine ⟨c, fun i => ⟨(hv (index i)).comp
    (htauPL.comp (originalStripSheet_finitePL i) (fun p hp => originalStripSheet_mem_tube i hp))
      (hdiag i), hci i, hcP i⟩, ?_, hcvalue, hgi, ?_⟩
  · apply disjoint_left.mpr
    rintro x ⟨p, hp, rfl⟩ ⟨q, hq, he⟩
    exact disjoint_left.mp hdisj (hcP false hp) (he ▸ hcP true hq)
  · ext x
    constructor
    · rintro ⟨hxD, z, hz, he⟩
      have hxC : f x ∈ C := he ▸ (g (tau z)).property
      have hxbranches := hconfine ⟨hxD, hxC⟩
      have hrecover (i : Bool) (hxP : x ∈ (P (index i)).space) : x ∈ c i '' source := by
        have hxT : x ∈ (T (index i)).space := (hclip _).symm.subset ⟨hxP, hxC⟩
        have hFx : F (f x) = tau z := (congrArg F he).symm.trans (hFg _ (htauK hz))
        have hzM : tau z ∈ (M (index i)).space := by
          rw [← hFx, ← himage]
          exact ⟨x, hxT, rfl⟩
        let p : P2 := (z.2, z.1.1)
        have hp : p ∈ source := ⟨hz.2, hz.1.1⟩
        have hd : originalStripSheet i p = z := by
          have hs := (hsheet (index i) z hz).mp hzM
          cases i <;> norm_num [index] at hs <;>
            exact Prod.ext (Prod.ext rfl hs.symm) rfl
        refine ⟨p, hp, ?_⟩
        apply hinj (index i) (hcP i hp) hxP
        rw [hcvalue i p hp, hd]
        exact he
      rcases hxbranches with hx0 | hx1
      · exact Or.inl (hrecover false hx0)
      · exact Or.inr (hrecover true hx1)
    · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
      · exact ⟨hPD 0 (hcP false hp), originalStripSheet false p,
          originalStripSheet_mem_tube false hp, (hcvalue false p hp).symm⟩
      · exact ⟨hPD 1 (hcP true hp), originalStripSheet true p,
          originalStripSheet_mem_tube true hp, (hcvalue true p hp).symm⟩

theorem exists_original_parameterized_tube_source_strips
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ))
    (C : Set X) (K : SimplicialComplex ℝ E)
    (F : X → E) (H : C ≃ₜ K.space) (g : E → C)
    (hH : ∀ x : C, (H x : E) = F x)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hgPL : PolyhedralPLInCharts e (fun z => (g z : X)) K.space)
    (hsep : ∀ x ∈ C, ∀ y : X, F x = F y → x = y)
    (P T : Fin 2 → SimplicialComplex ℝ V2)
    (M : Fin 2 → SimplicialComplex ℝ E) (f : V2 → X)
    (hinj : ∀ i, InjOn f (P i).space)
    (hclip : ∀ i, (T i).space = (P i).space ∩ f ⁻¹' C)
    (hPL : ∀ i, FinitePiecewiseAffineOn (F ∘ f) (T i).space)
    (himage : ∀ i, (F ∘ f) '' (T i).space = (M i).space)
    (hMK : ∀ i, M i ≤ K)
    {D : Set V2} (hPD : ∀ i, (P i).space ⊆ D)
    (hdisj : Disjoint (P 0).space (P 1).space)
    (hconfine : D ∩ f ⁻¹' C ⊆ (P 0).space ∪ (P 1).space)
    (tau : C3 → E) (htauPL : FinitePiecewiseAffineOn tau tube)
    (htaui : InjOn tau tube) (htauK : MapsTo tau tube K.space)
    (hsheet : ∀ i z, z ∈ tube →
      (tau z ∈ (M i).space ↔ z.1.2 = if i = 0 then z.1.1 else -z.1.1))
    (A : Fin 2 → Set V2) (alpha : ∀ i, Icc (0 : ℝ) 1 ≃ₜ A i)
    (hAP : ∀ i, A i ⊆ (P i).space)
    (haxis : ∀ i (t : Icc (0 : ℝ) 1), tau ((0, 0), t) = F (f (alpha i t))) :
    ∃ c : Bool → P2 → V2,
      (∀ i, FinitePiecewiseAffineOn (c i) source ∧
        Topology.IsEmbedding (fun p : source => c i p) ∧ MapsTo (c i) source D) ∧
      Disjoint (c false '' source) (c true '' source) ∧
      PolyhedralPLInCharts e (fun z => (g (tau z) : X)) tube ∧
      Topology.IsEmbedding (fun z : tube => (g (tau z) : X)) ∧
      (∀ i p, p ∈ source → f (c i p) = (g (tau (originalStripSheet i p)) : X)) ∧
      D ∩ f ⁻¹' ((fun z => (g (tau z) : X)) '' tube) =
        (c false '' source) ∪ (c true '' source) ∧
      (∀ i (t : Icc (0 : ℝ) 1), c i (t, 0) = alpha (if i then 1 else 0) t) ∧
      (∀ i, c i '' arm 0 = A (if i then 1 else 0)) ∧
      ∀ (Z : Set X) (Q : Set V2),
        (∀ x ∈ D, f x ∈ Z ↔ x ∈ Q) →
        (∀ z ∈ tube, (g (tau z) : X) ∈ Z ↔ z.2 = 0 ∨ z.2 = 1) →
        ∀ i p, p ∈ source → (c i p ∈ Q ↔ p.1 = 0 ∨ p.1 = 1) := by
  obtain ⟨c, hc, hcd, hcv, hti, hfull⟩ := exists_original_tube_source_strips
    C K F H g hH hg hsep P T M f hinj hclip hPL himage hMK hPD hdisj
      hconfine tau htauPL htaui htauK hsheet
  have hphysical : PolyhedralPLInCharts e (fun z => (g (tau z) : X)) tube := by
    obtain ⟨J, hJ, hJs, hJa⟩ := htauPL
    have hm : MapsTo tau J.space K.space := by simpa only [hJs] using htauK
    have hh := hgPL.comp_finitePiecewiseAffineOn J hJ
      (show FinitePiecewiseAffineOn tau J.space from ⟨J, hJ, rfl, hJa⟩) hm
    simpa only [hJs, Function.comp_def] using hh
  have hcompact : IsCompact source := isCompact_Icc.prod isCompact_Icc
  let : CompactSpace source := isCompact_iff_compactSpace.mp hcompact
  let : CompactSpace tube := isCompact_iff_compactSpace.mp
    ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc)
  have hce (i : Bool) : Topology.IsEmbedding (fun p : source => c i p) :=
    ((hc i).1.continuousOn.restrict.isClosedEmbedding (fun p q he =>
      Subtype.ext ((hc i).2.1 p.property q.property he))).isEmbedding
  have hte : Topology.IsEmbedding (fun z : tube => (g (tau z) : X)) :=
    (hphysical.continuousOn.restrict.isClosedEmbedding (fun z w he =>
      Subtype.ext (hti z.property w.property he))).isEmbedding
  have hcD (i : Bool) : MapsTo (c i) source D := fun p hp => hPD _ ((hc i).2.2 hp)
  have hcenter (i : Bool) (t : Icc (0 : ℝ) 1) :
      c i (t, 0) = alpha (if i then 1 else 0) t := by
    have hp : ((t : ℝ), (0 : ℝ)) ∈ source := ⟨t.property, by norm_num⟩
    apply hinj (if i then 1 else 0) ((hc i).2.2 hp) (hAP _ (alpha _ t).property)
    rw [hcv i _ hp]
    have hd : originalStripSheet i ((t : ℝ), 0) = (((0, 0), (t : ℝ)) : C3) := by
      cases i <;> simp [originalStripSheet]
    rw [hd]
    apply hsep _ (g _).property
    have hz : ((0, 0), (t : ℝ)) ∈ tube := ⟨⟨by norm_num, by norm_num⟩, t.property⟩
    have hgF : F (g (tau ((0, 0), t))) = tau ((0, 0), t) := by
      rw [← hH (g _)]
      have he : g (tau ((0, 0), t)) = H.symm ⟨tau ((0, 0), t), htauK hz⟩ :=
        Subtype.ext (hg ⟨tau ((0, 0), t), htauK hz⟩)
      rw [he, H.apply_symm_apply]
    exact hgF.trans (haxis _ t)
  refine ⟨c, fun i => ⟨(hc i).1, hce i, hcD i⟩, hcd, hphysical, hte, hcv,
    hfull, hcenter, ?_, ?_⟩
  · intro i
    ext x
    constructor
    · rintro ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
      change u = 0 at hu
      subst u
      rw [hcenter i ⟨t, ht⟩]
      exact (alpha _ _).property
    · intro hx
      let t := (alpha (if i then 1 else 0)).symm ⟨x, hx⟩
      refine ⟨(t, 0), ⟨t.property, rfl⟩, ?_⟩
      exact (hcenter i t).trans (congrArg Subtype.val ((alpha _).apply_symm_apply ⟨x, hx⟩))
  · intro Z Q hfQ htQ i p hp
    rw [← hfQ _ (hcD i hp), hcv i p hp, htQ _ (originalStripSheet_mem_tube i hp)]
    rfl

end PoincareConjecture.M76.Dehn
