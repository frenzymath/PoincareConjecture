import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsAnnularEvolution
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NonnestedHeightLiftImage













set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

local notation "P" => (ℝ × E2)
local notation "SP" => (ℝ × (ℝ × E2))
local notation "D2" => Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞
local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞





theorem exists_nonnested_annular_height_lift_image
    (Phi : ℝ → Diffeomorph 𝓘(ℝ, P) 𝓘(ℝ, P) P P ∞)
    (H : ℝ → ℝ → (E2 ≃ₜ E2))
    (S : Set P) (hSc : IsCompact S)
    (hPhi : ContDiff ℝ ∞ (fun p : SP => Phi p.1 p.2))
    (hPhii : ContDiff ℝ ∞ (fun p : SP => (Phi p.1).symm p.2))
    (hPhi0 : ∀ p : P, Phi 0 p = p)
    (hFiber : ∀ t z : ℝ, ∀ x : E2,
      H t z x = (Phi t (z, x)).2 ∧
        (H t z).symm x = ((Phi t).symm (z, x)).2)
    (hFix : ∀ t : ℝ, ∀ p : P, p ∉ S →
      Phi t p = p ∧ (Phi t).symm p = p)
    (chi : ℝ → ℝ) (hchi : ContDiff ℝ ∞ chi)
    (hsChi : HasCompactSupport chi) (u : UnitTwoSphere)
    (sourceSlice targetSlice : ℝ → Set E2)
    (himage : ∀ z : ℝ,
      H (chi z) z '' sourceSlice z = targetSlice z) :
    let C : Set E2 := Prod.snd '' S
    let L := heightPlaneCoordinates u
    ∃ G : D3,
      (∀ x : E2, ∀ z : ℝ,
        G (L.symm (x, z)) = L.symm (H (chi z) z x, z) ∧
        G.symm (L.symm (x, z)) =
          L.symm ((H (chi z) z).symm x, z)) ∧
      IsCompact (L.symm '' (C ×ˢ tsupport chi)) ∧
      tsupport (fun y : E3 => G y - y) ⊆
        L.symm '' (C ×ˢ tsupport chi) ∧
      tsupport (fun y : E3 => G.symm y - y) ⊆
        L.symm '' (C ×ˢ tsupport chi) ∧
      G '' (L.symm '' (⋃ z : ℝ, sourceSlice z ×ˢ ({z} : Set ℝ))) =
        L.symm '' (⋃ z : ℝ, targetSlice z ×ˢ ({z} : Set ℝ)) ∧
      G.symm '' (L.symm '' (⋃ z : ℝ, targetSlice z ×ˢ ({z} : Set ℝ))) =
        L.symm '' (⋃ z : ℝ, sourceSlice z ×ˢ ({z} : Set ℝ)) := by
  dsimp only
  let C : Set E2 := Prod.snd '' S
  have hH : ContDiff ℝ ∞
      (fun p : SP => H p.1 p.2.1 p.2.2) := by
    have hs : ContDiff ℝ ∞ (fun p : SP => (Phi p.1 p.2).2) := hPhi.snd
    convert hs using 1
    funext p
    exact (hFiber p.1 p.2.1 p.2.2).1
  have hHi : ContDiff ℝ ∞
      (fun p : SP => (H p.1 p.2.1).symm p.2.2) := by
    have hs : ContDiff ℝ ∞ (fun p : SP => ((Phi p.1).symm p.2).2) :=
      hPhii.snd
    convert hs using 1
    funext p
    exact (hFiber p.1 p.2.1 p.2.2).2
  let F : ℝ → D2 := fun z =>
    { toEquiv := H (chi z) z
      contMDiff_toFun := by
        have hs : ContDiff ℝ ∞ (fun x : E2 => H (chi z) z x) :=
          hH.comp (contDiff_const.prodMk
            (contDiff_const.prodMk contDiff_id))
        exact hs.contMDiff
      contMDiff_invFun := by
        have hs : ContDiff ℝ ∞
            (fun x : E2 => (H (chi z) z).symm x) :=
          hHi.comp (contDiff_const.prodMk
            (contDiff_const.prodMk contDiff_id))
        exact hs.contMDiff }
  have hF : ContDiff ℝ ∞ (fun p : ℝ × E2 => F p.1 p.2) := by
    change ContDiff ℝ ∞ (fun p : ℝ × E2 => H (chi p.1) p.1 p.2)
    exact hH.comp ((hchi.comp contDiff_fst).prodMk
      (contDiff_fst.prodMk contDiff_snd))
  have hFi : ContDiff ℝ ∞
      (fun p : ℝ × E2 => (F p.1).symm p.2) := by
    change ContDiff ℝ ∞ (fun p : ℝ × E2 =>
      (H (chi p.1) p.1).symm p.2)
    exact hHi.comp ((hchi.comp contDiff_fst).prodMk
      (contDiff_fst.prodMk contDiff_snd))
  have hFzero (z : ℝ) (x : E2) (hz : chi z = 0) : F z x = x := by
    change H (chi z) z x = x
    rw [hz]
    calc
      H 0 z x = (Phi 0 (z, x)).2 := (hFiber 0 z x).1
      _ = x := by rw [hPhi0]
  have hFinvzero (z : ℝ) (x : E2) (hz : chi z = 0) :
      (F z).symm x = x := by
    change (H (chi z) z).symm x = x
    rw [hz]
    calc
      (H 0 z).symm x = ((Phi 0).symm (z, x)).2 := (hFiber 0 z x).2
      _ = x := by
        have hp := (Phi 0).symm_apply_apply (z, x)
        rw [hPhi0 (z, x)] at hp
        exact congrArg Prod.snd hp
  have hC : IsCompact C := by
    exact hSc.image continuous_snd
  have hfix : ∀ t : ℝ, ∀ x : E2, x ∉ C → F t x = x := by
    intro t x hx
    change H (chi t) t x = x
    have hp : (t, x) ∉ S := by
      intro htx
      exact hx ⟨(t, x), htx, rfl⟩
    rw [(hFiber (chi t) t x).1]
    exact congrArg Prod.snd (hFix (chi t) (t, x) hp).1
  have hfixInv : ∀ t : ℝ, ∀ x : E2, x ∉ C → (F t).symm x = x := by
    intro t x hx
    change (H (chi t) t).symm x = x
    have hp : (t, x) ∉ S := by
      intro htx
      exact hx ⟨(t, x), htx, rfl⟩
    rw [(hFiber (chi t) t x).2]
    exact congrArg Prod.snd (hFix (chi t) (t, x) hp).2
  have hFimage : ∀ z : ℝ, F z '' sourceSlice z = targetSlice z := by
    intro z
    change H (chi z) z '' sourceSlice z = targetSlice z
    exact himage z
  let L := heightPlaneCoordinates u
  let K : Set E3 := L.symm '' (C ×ˢ tsupport chi)
  let sourceStack : Set (E2 × ℝ) :=
    ⋃ z : ℝ, sourceSlice z ×ˢ ({z} : Set ℝ)
  let targetStack : Set (E2 × ℝ) :=
    ⋃ z : ℝ, targetSlice z ×ˢ ({z} : Set ℝ)
  let Q := planarFamilyGraphDiffeomorph F hF hFi
  let G : D3 := (L.toDiffeomorph.trans Q).trans L.symm.toDiffeomorph
  have hformula (x : E2) (z : ℝ) :
      G (L.symm (x, z)) = L.symm (F z x, z) ∧
      G.symm (L.symm (x, z)) = L.symm ((F z).symm x, z) := by
    constructor
    · change L.symm (Q (L (L.symm (x, z)))) = _
      rw [L.apply_symm_apply]
      rfl
    · change L.symm (Q.symm (L (L.symm (x, z)))) = _
      rw [L.apply_symm_apply]
      rfl
  have hK : IsCompact K :=
    (hC.prod hsChi.isCompact).image L.symm.continuous
  have hboth (y : E3) (hy : y ∉ K) : G y = y ∧ G.symm y = y := by
    let x : E2 := (L y).1
    let z : ℝ := (L y).2
    have hcoord : L.symm (x, z) = y := L.symm_apply_apply y
    obtain ⟨hf, hi⟩ := hformula x z
    by_cases hx : x ∈ C
    · have hz : z ∉ tsupport chi := by
        intro hz
        exact hy ⟨(x, z), ⟨hx, hz⟩, hcoord⟩
      have hc : chi z = 0 := image_eq_zero_of_notMem_tsupport hz
      have hf0 : F z x = x := hFzero z x hc
      have hi0 : (F z).symm x = x := hFinvzero z x hc
      rw [hf0, hcoord] at hf
      rw [hi0, hcoord] at hi
      exact ⟨hf, hi⟩
    · rw [hfix z x hx, hcoord] at hf
      rw [hfixInv z x hx, hcoord] at hi
      exact ⟨hf, hi⟩
  have hforward : G '' (L.symm '' sourceStack) = L.symm '' targetStack := by
    ext y
    constructor
    · rintro ⟨v, ⟨p, hp, rfl⟩, rfl⟩
      rcases mem_iUnion.mp hp with ⟨z, hz⟩
      rcases hz with ⟨hx, htz⟩
      rcases p with ⟨x, t⟩
      change x ∈ sourceSlice z at hx
      have ht : t = z := by simpa using htz
      subst t
      refine ⟨(F z x, z), ?_, (hformula x z).1.symm⟩
      refine mem_iUnion.mpr ⟨z, ⟨?_, rfl⟩⟩
      rw [← hFimage z]
      exact ⟨x, hx, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      rcases mem_iUnion.mp hp with ⟨z, hz⟩
      rcases hz with ⟨hx, htz⟩
      rcases p with ⟨x, t⟩
      change x ∈ targetSlice z at hx
      have ht : t = z := by simpa using htz
      subst t
      have hxi : (F z).symm x ∈ sourceSlice z := by
        have hx' : x ∈ F z '' sourceSlice z := by
          rw [hFimage z]
          exact hx
        rcases hx' with ⟨y, hy, hyx⟩
        rw [← hyx]
        simpa only [(F z).symm_apply_apply] using hy
      refine ⟨L.symm ((F z).symm x, z), ?_, ?_⟩
      · refine ⟨((F z).symm x, z), ?_, rfl⟩
        exact mem_iUnion.mpr ⟨z, ⟨hxi, rfl⟩⟩
      · rw [(hformula ((F z).symm x) z).1]
        simp only [(F z).apply_symm_apply]
  have hinverse : G.symm '' (L.symm '' targetStack) = L.symm '' sourceStack := by
    ext y
    constructor
    · rintro ⟨v, ⟨p, hp, rfl⟩, rfl⟩
      rcases mem_iUnion.mp hp with ⟨z, hz⟩
      rcases hz with ⟨hx, htz⟩
      rcases p with ⟨x, t⟩
      change x ∈ targetSlice z at hx
      have ht : t = z := by simpa using htz
      subst t
      have hxi : (F z).symm x ∈ sourceSlice z := by
        have hx' : x ∈ F z '' sourceSlice z := by
          rw [hFimage z]
          exact hx
        rcases hx' with ⟨y, hy, hyx⟩
        rw [← hyx]
        simpa only [(F z).symm_apply_apply] using hy
      refine ⟨((F z).symm x, z), ?_, (hformula x z).2.symm⟩
      exact mem_iUnion.mpr ⟨z, ⟨hxi, rfl⟩⟩
    · rintro ⟨p, hp, rfl⟩
      rcases mem_iUnion.mp hp with ⟨z, hz⟩
      rcases hz with ⟨hx, htz⟩
      rcases p with ⟨x, t⟩
      change x ∈ sourceSlice z at hx
      have ht : t = z := by simpa using htz
      subst t
      refine ⟨L.symm (F z x, z), ?_, ?_⟩
      · refine ⟨(F z x, z), ?_, rfl⟩
        refine mem_iUnion.mpr ⟨z, ⟨?_, rfl⟩⟩
        rw [← hFimage z]
        exact ⟨x, hx, rfl⟩
      · rw [(hformula (F z x) z).2]
        simp only [(F z).symm_apply_apply]
  refine ⟨G, ?_, hK, ?_, ?_, ?_, ?_⟩
  · intro x z
    change G (L.symm (x, z)) = L.symm (F z x, z) ∧
      G.symm (L.symm (x, z)) = L.symm ((F z).symm x, z)
    exact hformula x z
  · apply closure_minimal ?_ hK.isClosed
    intro y hy
    by_contra hyK
    exact hy (sub_eq_zero.mpr (hboth y hyK).1)
  · apply closure_minimal ?_ hK.isClosed
    intro y hy
    by_contra hyK
    exact hy (sub_eq_zero.mpr (hboth y hyK).2)
  · exact hforward
  · exact hinverse

end PoincareConjecture.M25.Topology3D
