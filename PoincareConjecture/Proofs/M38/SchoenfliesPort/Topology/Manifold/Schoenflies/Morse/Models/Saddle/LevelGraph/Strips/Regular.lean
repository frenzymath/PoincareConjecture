import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.RegularLevel.Tube

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SaddleLevel

open Poincare.Geometry.Manifold.RegularLevel

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)
local notation "IR2" => 𝓘(Real, Real × Real)
private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩
private instance : ChartedSpace (E1 × Real) (S1 × Real) :=
  prodChartedSpace E1 S1 Real Real

private theorem exists_strip_chart_of_injective_bijective_derivative
    {G : Real × Real -> S2} {s : Set (Real × Real)} (hs : IsOpen s)
    (hG : ContMDiffOn IR2 (𝓡 2) ∞ G s) (hinj : InjOn G s)
    (hbij : ∀ z ∈ s, Function.Bijective (mfderiv IR2 (𝓡 2) G z)) :
    ∃ e : OpenPartialHomeomorph (Real × Real) S2,
      e.source = s ∧ (e : Real × Real -> S2) = G ∧
      ContMDiffOn IR2 (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) IR2 ∞ e.symm e.target := by
  let U : Opens (Real × Real) := ⟨s, hs⟩
  have hGu : ContMDiff IR2 (𝓡 2) ∞ (fun z : U => G z) := by
    intro z
    exact (hG.contMDiffAt (hs.mem_nhds z.property)).comp z (contMDiff_subtype_val z)
  have hbu (z : U) : Function.Bijective (mfderiv IR2 (𝓡 2) (fun w : U => G w) z) := by
    rw [mfderiv_opens_restrict U G
      ((hG.contMDiffAt (hs.mem_nhds z.property)).mdifferentiableAt (by simp))]
    exact hbij z z.property
  have hopen : IsOpenMap (fun z : U => G z) := by
    apply IsOpenMap.of_nhds_le
    intro z
    exact (Poincare.Geometry.Manifold.map_nhds_eq_of_contMDiffAt_bijective_mfderiv_modelSpaces
      (hGu z) (hbu z)).ge
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict
    (hinj.toPartialEquiv G s) hG.continuousOn hopen hs
  refine ⟨e, rfl, rfl, hG, ?_⟩
  intro y hy
  have hx : e.symm y ∈ s := e.map_target hy
  have hleft : ∀ᶠ z in 𝓝 (e.symm y), e.symm (G z) = z := by
    filter_upwards [hs.mem_nhds hx] with z hz
    exact e.left_inv hz
  have hInv := Poincare.Geometry.Manifold.contMDiffAt_of_local_left_inverse_modelSpaces
    (hG.contMDiffAt (hs.mem_nhds hx)) (hbij _ hx) hleft
  rw [show G (e.symm y) = y from e.right_inv hy] at hInv
  exact hInv.contMDiffWithinAt

theorem exists_regular_level_interval_strip
    {H : S2 -> Real} (hH : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ H)
    (c : Real) (hreg : ∀ q, H q = c -> mfderiv (𝓡 2) 𝓘(Real, Real) H q ≠ 0)
    (p : S2) (hp : H p = c) (γ : Real -> S2)
    (hγ : ContMDiff 𝓘(Real, Real) (𝓡 2) ∞ γ) (hγinj : Function.Injective γ)
    (hγder : ∀ t, Function.Injective (mfderiv 𝓘(Real, Real) (𝓡 2) γ t))
    (hγC : range γ ⊆ connectedComponentIn (H ⁻¹' {c}) p) :
    ∃ ε : Real, 0 < ε ∧ ∃ e : OpenPartialHomeomorph (Real × Real) S2,
      e.source = univ ×ˢ Ioo (-ε) ε ∧
      ContMDiffOn IR2 (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) IR2 ∞ e.symm e.target ∧
      (∀ s, e (s, 0) = γ s) ∧
      ∀ s t, t ∈ Ioo (-ε) ε -> H (e (s, t)) = c + t := by
  obtain ⟨ε, hε, F, hFs, hF, hFi, hheight, hcentral⟩ :=
    exists_smooth_regular_level_component_tube_of_smooth hH c hreg p hp
  have hs0 (q : S1) : (q, (0 : Real)) ∈ F.source := by
    rw [hFs]
    exact ⟨mem_univ _, by constructor <;> linarith⟩
  have hγtarget (s : Real) : γ s ∈ F.target := by
    obtain ⟨q, hq⟩ := hcentral.symm ▸ hγC (mem_range_self s)
    rw [← hq]
    exact F.map_source (hs0 q)
  let k : Real -> S1 := fun s => (F.symm (γ s)).1
  have hpair (s : Real) : F.symm (γ s) = (k s, 0) := by
    obtain ⟨q, hq⟩ := hcentral.symm ▸ hγC (mem_range_self s)
    apply Prod.ext
    · rfl
    · rw [← hq, F.left_inv (hs0 q)]
  have hback (s : Real) : F (k s, 0) = γ s := by
    rw [← hpair s, F.right_inv (hγtarget s)]
  have hk : ContMDiff 𝓘(Real, Real) (𝓡 1) ∞ k := by
    intro s
    exact contMDiffAt_fst.comp s
      ((hFi.contMDiffAt (F.open_target.mem_nhds (hγtarget s))).comp s (hγ s))
  have hki : Function.Injective k := by
    intro s t hst
    apply hγinj
    rw [← hback s, ← hback t, hst]
  have hkd (s : Real) : Function.Injective (mfderiv 𝓘(Real, Real) (𝓡 1) k s) := by
    have heq : γ = F ∘ (fun s => (k s, (0 : Real))) := funext fun s => (hback s).symm
    have hdγ := hγder s
    rw [heq, mfderiv_comp s
      ((hF.contMDiffAt (F.open_source.mem_nhds (hs0 (k s)))).mdifferentiableAt (by simp))
      (((hk.prodMk contMDiff_const) s).mdifferentiableAt (by simp)),
      mfderiv_prodMk (hk.mdifferentiable (by simp) s) mdifferentiableAt_const,
      mfderiv_const] at hdγ
    intro u v huv
    apply hdγ
    exact congrArg (mfderiv Iprod (𝓡 2) F (k s, 0)) (Prod.ext huv rfl)
  let Q : Real × Real -> S1 × Real := Prod.map k id
  have hQ : ContMDiff IR2 Iprod ∞ Q := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hk.prodMap (contMDiff_id (I := 𝓘(Real, Real)))
  have hQi : Function.Injective Q := by
    intro z w hzw
    change (k z.1, z.2) = (k w.1, w.2) at hzw
    have hh := Prod.mk.inj hzw
    exact Prod.ext (hki hh.1) hh.2
  have hQd (z : Real × Real) : Function.Bijective (mfderiv IR2 Iprod Q z) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    dsimp only [Q]
    rw [mfderiv_prodMap (hk.mdifferentiable (by simp) z.1) mdifferentiableAt_id, mfderiv_id]
    have hsurj : Function.Surjective (mfderiv 𝓘(Real, Real) (𝓡 1) k z.1) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (V := Real) (V₂ := E1) (by simp)).mp (hkd z.1)
    constructor
    · intro u v huv
      change (mfderiv 𝓘(Real, Real) (𝓡 1) k z.1 u.1, u.2) =
        (mfderiv 𝓘(Real, Real) (𝓡 1) k z.1 v.1, v.2) at huv
      exact Prod.ext (hkd z.1 (Prod.mk.inj huv).1) (Prod.mk.inj huv).2
    · rintro ⟨u, v⟩
      obtain ⟨w, hw⟩ := hsurj u
      exact ⟨(w, v), Prod.ext hw rfl⟩
  let s : Set (Real × Real) := univ ×ˢ Ioo (-ε) ε
  have hs : IsOpen s := isOpen_univ.prod isOpen_Ioo
  have hQs : MapsTo Q s F.source := by
    intro z hz
    rw [hFs]
    exact ⟨mem_univ _, hz.2⟩
  have hG : ContMDiffOn IR2 (𝓡 2) ∞ (F ∘ Q) s := hF.comp hQ.contMDiffOn hQs
  have hGi : InjOn (F ∘ Q) s := by
    intro z hz w hw heq
    exact hQi (F.injOn (hQs hz) (hQs hw) heq)
  have hFd : F.MDifferentiable Iprod (𝓡 2) :=
    ⟨hF.mdifferentiableOn (by simp), hFi.mdifferentiableOn (by simp)⟩
  have hGd (z : Real × Real) (hz : z ∈ s) :
      Function.Bijective (mfderiv IR2 (𝓡 2) (F ∘ Q) z) := by
    rw [mfderiv_comp z (hFd.mdifferentiableAt (hQs hz)) (hQ.mdifferentiable (by simp) z)]
    exact (hFd.mfderiv_bijective (hQs hz)).comp (hQd z)
  obtain ⟨e, hes, heq, he, hei⟩ :=
    exists_strip_chart_of_injective_bijective_derivative hs hG hGi hGd
  refine ⟨ε, hε, e, hes, he, hei, ?_, ?_⟩
  · intro t
    rw [heq]
    exact hback t
  · intro u t ht
    rw [heq]
    exact hheight (k u) t ht

end Poincare.Manifold.Schoenflies.SaddleLevel

end

end M38Schoenflies
