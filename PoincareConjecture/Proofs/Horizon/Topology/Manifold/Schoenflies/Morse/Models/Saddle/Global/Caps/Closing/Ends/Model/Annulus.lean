import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.RegularLevel.SublevelExtension
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Extremum.BandCoverage
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.EndBall.TerminalHeight



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1
local notation "IP" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)




theorem exists_morse_disk_and_physical_annulus_cover
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (d : OpenPartialHomeomorph E2 S2) (hds : closedBall 0 1 ⊆ d.source)
    {p : S2} (hp : p ∈ d '' closedBall 0 1) {b : Real} (hpb : h p < b)
    (hboundary : ∀ x ∈ sphere (0 : E2) 1, h (d x) = b)
    (hunique : ∀ x ∈ d '' closedBall 0 1,
      mfderiv (𝓡 2) 𝓘(Real, Real) h x = 0 → x = p)
    (seed : S2)
    (hcomponent : d '' closedBall 0 1 = closure (connectedComponentIn (h ⁻¹' Iio b) seed))
    (hregular : ∀ q, h q = b → mfderiv (𝓡 2) 𝓘(Real, Real) h q ≠ 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (hform : ∀ x ∈ e.source, h (e x) = h p + ‖x‖ ^ 2) :
    ∃ R : Real, 0 < R ∧ h p + R ^ 2 < b ∧
      closedBall (0 : E2) R ⊆ e.source ∧
      ∀ r ∈ Ioc (0 : Real) R,
        ∃ δ : Real, 0 < δ ∧ ∃ F : OpenPartialHomeomorph (S1 × Real) S2,
          F.source = univ ×ˢ Ioo (h p + r ^ 2 - δ) (b + δ) ∧
          ContMDiffOn IP (𝓡 2) ∞ F F.source ∧
          ContMDiffOn (𝓡 2) IP ∞ F.symm F.target ∧
          (∀ q t, t ∈ Ioo (h p + r ^ 2 - δ) (b + δ) → h (F (q, t)) = t) ∧
          range (fun q : S1 => F (q, h p + r ^ 2)) = e '' sphere (0 : E2) r ∧
          F '' (univ ×ˢ Icc (h p + r ^ 2) b) =
            (d '' closedBall 0 1) \ (e '' ball (0 : E2) r) ∧
          d '' closedBall 0 1 =
            e '' closedBall (0 : E2) r ∪ F '' (univ ×ˢ Icc (h p + r ^ 2) b) := by
  obtain ⟨k, hk, hnear, habove⟩ :=
    exists_height_extension_above_sublevel_component hh seed b hregular
  have hgerm (x : S2) (hx : x ∈ d '' closedBall 0 1) : k =ᶠ[𝓝 x] h :=
    hnear.filter_mono (nhds_le_nhdsSet (hcomponent ▸ hx))
  have heq (x : S2) (hx : x ∈ d '' closedBall 0 1) : k x = h x :=
    (hgerm x hx).eq_of_nhds
  have hkp : k p = h p := heq p hp
  have hnearzero : ∀ᶠ x in 𝓝 (0 : E2), x ∈ e.source ∧ k (e x) = h (e x) := by
    have hcomp := (e.continuousAt he0).eventually (show k =ᶠ[𝓝 (e 0)] h by rw [hep]; exact hgerm p hp)
    have hs : ∀ᶠ x in 𝓝 (0 : E2), x ∈ e.source := e.open_source.mem_nhds he0
    exact hs.and hcomp
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hnearzero
  let e' := e.restrOpen (ball (0 : E2) ε) isOpen_ball
  have he'0 : 0 ∈ e'.source := ⟨he0, mem_ball_self hε⟩
  have he'form (x : E2) (hx : x ∈ e'.source) : k (e' x) = k p + ‖x‖ ^ 2 := by
    change k (e x) = k p + ‖x‖ ^ 2
    rw [(hεsub hx.2).2, hkp, hform x hx.1]
  obtain ⟨R, hR, hRb, hRs, hfamily⟩ := exists_morse_disk_and_annulus_cover hk d hds hp
    (by rwa [hkp])
    (fun x hx => (heq _ (mem_image_of_mem d (sphere_subset_closedBall hx))).trans (hboundary x hx))
    (fun x hx hc => hunique x hx (by rw [← (hgerm x hx).mfderiv_eq]; exact hc))
    (fun x hx => habove x (by rwa [← hcomponent])) e' he'0 hep he'form
  rw [hkp] at hRb hfamily
  refine ⟨R, hR, hRb, fun x hx => (hRs hx).1, ?_⟩
  intro r hr
  obtain ⟨δ, hδ, F, hFs, hF, hFi, hheight, hcenter, hband, hcover⟩ := hfamily r hr
  let c := h p + r ^ 2
  have hcb : c < b := by
    have hs := (sq_le_sq₀ hr.1.le hR.le).mpr hr.2
    dsimp [c]
    linarith
  have hsource (q : S1) (t : Real) (ht : t ∈ Icc c b) : (q, t) ∈ F.source := by
    rw [hFs]
    exact ⟨mem_univ _, by linarith [ht.1], by linarith [ht.2]⟩
  have hmem (q : S1) (t : Real) (ht : t ∈ Icc c b) : F (q, t) ∈ d '' closedBall 0 1 := by
    have hm : F (q, t) ∈ F '' (univ ×ˢ Icc (h p + r ^ 2) b) :=
      mem_image_of_mem F ⟨mem_univ _, ht⟩
    rw [hband] at hm
    exact hm.1
  have hphysical (q : S1) (t : Real) (ht : t ∈ Icc c b) : h (F (q, t)) = t :=
    (heq _ (hmem q t ht)).symm.trans
      (hheight q t ((hFs ▸ hsource q t ht).2))
  have hheight' (q : S1) (t : Real) (ht : (q, t) ∈ F.source) : k (F (q, t)) = t :=
    hheight q t (hFs ▸ ht).2
  obtain ⟨εc, hεc, _, hhc⟩ := Saddle.Caps.exists_physical_height_interval_of_germ F k h
    (fun q => hsource q c ⟨le_rfl, hcb.le⟩) hheight'
    (fun q => hgerm _ (hmem q c ⟨le_rfl, hcb.le⟩))
  obtain ⟨εb, hεb, _, hhb⟩ := Saddle.Caps.exists_physical_height_interval_of_germ F k h
    (fun q => hsource q b ⟨hcb.le, le_rfl⟩) hheight'
    (fun q => hgerm _ (hmem q b ⟨hcb.le, le_rfl⟩))
  let δ' := min δ (min εc εb)
  have hδ' : 0 < δ' := lt_min hδ (lt_min hεc hεb)
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  have hδ'c : δ' ≤ εc := (min_le_right _ _).trans (min_le_left _ _)
  have hδ'b : δ' ≤ εb := (min_le_right _ _).trans (min_le_right _ _)
  let W : Set (S1 × Real) := univ ×ˢ Ioo (c - δ') (b + δ')
  have hWs : W ⊆ F.source := by
    rintro ⟨q, t⟩ ⟨_, ht⟩
    rw [hFs]
    exact ⟨mem_univ _, by linarith [ht.1], by linarith [ht.2]⟩
  let F' := F.restrOpen W (isOpen_univ.prod isOpen_Ioo)
  refine ⟨δ', hδ', F', inter_eq_right.mpr hWs,
    hF.mono inter_subset_left, hFi.mono inter_subset_left, ?_, hcenter, hband, hcover⟩
  intro q t ht
  change h (F (q, t)) = t
  by_cases htc : t < c
  · exact hhc q t ⟨by linarith [ht.1], by linarith⟩
  by_cases hbt : b < t
  · exact hhb q t ⟨by linarith, by linarith [ht.2]⟩
  exact hphysical q t ⟨le_of_not_gt htc, le_of_not_gt hbt⟩

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
