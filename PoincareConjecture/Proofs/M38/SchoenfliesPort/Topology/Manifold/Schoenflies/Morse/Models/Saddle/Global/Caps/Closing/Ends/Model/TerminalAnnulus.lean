import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.Model.Coordinates
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.Model.Annulus







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "IP" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)
open SaddleLevel

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

private theorem model_closure_strict_component
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {b : Real} {q : S2} (hq : h q < b)
    (hreg : ∀ x, h x = b → mfderiv (𝓡 2) 𝓘(Real, Real) h x ≠ 0) :
    closure (connectedComponentIn (h ⁻¹' Iio b) q) =
      connectedComponentIn (h ⁻¹' Iic b) q := by
  let : LocallyConnectedSpace S2 := ChartedSpace.locallyConnectedSpace E2 S2
  have heq := Poincare.Topology.connectedComponentIn_sublevel_eq_closure_strict_sublevel
    (O := univ) isOpen_univ hh.continuous.continuousOn (mem_univ q) hq
    (subset_univ _) (fun x _ hxb => Or.inr (by
      simpa only [hxb] using
        Poincare.Geometry.Manifold.hasConnectedLowerSide_of_regular hh isOpen_univ
          (mem_univ x) (hreg x hxb)))
  simpa only [univ_inter] using heq.symm




theorem exists_terminal_model_oriented_morse_cap
    (data : TerminalSaddleData M P p e) (i : Fin 3) :
    let H : S2 → Real := fun q => inner Real (M.v : E3)
      (data.toTerminalSaddleGeometry.filledModel q)
    ∃ h : S2 → Real, ∃ b : Real, ∃ q : S2, ∃ C : OpenPartialHomeomorph E2 S2,
      ((h = H ∧ b = data.ends.lowerCut) ∨
        (h = -H ∧ b = -data.ends.upperCut)) ∧
      ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h ∧
      q ∈ data.modelDisk i '' closedBall (0 : E2) 1 ∧ h q < b ∧
      (∀ x ∈ sphere (0 : E2) 1, h (data.modelDisk i x) = b) ∧
      (∀ x ∈ data.modelDisk i '' closedBall (0 : E2) 1,
        mfderiv (𝓡 2) 𝓘(Real, Real) h x = 0 → x = q) ∧
      data.modelDisk i '' closedBall (0 : E2) 1 =
        closure (connectedComponentIn (h ⁻¹' Iio b) (data.modelSeed i)) ∧
      (∀ x, h x = b → mfderiv (𝓡 2) 𝓘(Real, Real) h x ≠ 0) ∧
      0 ∈ C.source ∧ C 0 = q ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target ∧
      ∀ x ∈ C.source, h (C x) = h q + ‖x‖^2 := by
  let H : S2 → Real := fun q => inner Real (M.v : E3)
    (data.toTerminalSaddleGeometry.filledModel q)
  have hH : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ H :=
    (innerSL Real (M.v : E3)).contMDiff.comp
      (data.toTerminalSaddleGeometry.filledModel.contMDiff.comp contMDiff_coe_sphere)
  have hab : data.ends.lowerCut ≤ data.ends.upperCut := by
    rw [data.lowerCut_eq, data.upperCut_eq]
    linarith [data.eta_pos]
  obtain ⟨q, hqK, hqc, C, hC0, hCq, hC, hCi, hcases⟩ :=
    exists_terminal_model_extremum_coordinates data i
  have huniq : ∀ x ∈ data.modelDisk i '' closedBall (0 : E2) 1,
      mfderiv (𝓡 2) 𝓘(Real, Real) H x = 0 → x = q := by
    obtain ⟨r, hr, hru⟩ := existsUnique_critical_in_terminal_model_cap data i
    intro x hx hc
    exact (hru x ⟨data.modelDisk_image i ▸ hx, hc⟩).trans (hru q ⟨hqK, hqc⟩).symm
  have hqD : q ∈ data.modelDisk i '' closedBall (0 : E2) 1 := data.modelDisk_image i ▸ hqK
  rcases hcases with ⟨hlo, hform⟩ | ⟨hhi, hform⟩
  · have hcomp := (terminal_model_domain_component data i).resolve_right (by
      rintro ⟨_, heq⟩
      have hle : data.ends.upperCut ≤ H q :=
        connectedComponentIn_subset (H ⁻¹' Ici data.ends.upperCut) (data.modelSeed i) (heq ▸ hqK)
      exact (hlo.not_ge (hab.trans hle)))
    have hboundary := (terminal_model_domain_boundary data i).resolve_right
      (fun hx => (not_lt_of_ge (hcomp.1.le.trans hab)) hx.1)
    have hregular : ∀ x, H x = data.ends.lowerCut →
        mfderiv (𝓡 2) 𝓘(Real, Real) H x ≠ 0 :=
      fun x hx => terminal_model_cut_regular data x (Or.inl hx)
    refine ⟨H, data.ends.lowerCut, q, C, Or.inl ⟨rfl, rfl⟩, hH,
      hqD, hlo, hboundary.2, huniq, ?_, hregular, hC0, hCq, hC, hCi, hform⟩
    rw [data.modelDisk_image, hcomp.2, model_closure_strict_component hH hcomp.1 hregular]
  · have hcomp := (terminal_model_domain_component data i).resolve_left (by
      rintro ⟨_, heq⟩
      have hle : H q ≤ data.ends.lowerCut :=
        connectedComponentIn_subset (H ⁻¹' Iic data.ends.lowerCut) (data.modelSeed i) (heq ▸ hqK)
      exact hhi.not_ge (hle.trans hab))
    have hboundary := (terminal_model_domain_boundary data i).resolve_left
      (fun hx => (not_lt_of_ge (hab.trans hcomp.1.le)) hx.1)
    have hregular : ∀ x, (-H) x = -data.ends.upperCut →
        mfderiv (𝓡 2) 𝓘(Real, Real) (-H) x ≠ 0 := by
      intro x hx
      rw [mfderiv_neg]
      exact neg_ne_zero.mpr (terminal_model_cut_regular data x (Or.inr (neg_injective hx)))
    refine ⟨-H, -data.ends.upperCut, q, C, Or.inr ⟨rfl, rfl⟩, hH.neg,
      hqD, neg_lt_neg hhi, (fun x hx => congrArg Neg.neg (hboundary.2 x hx)),
      ?_, ?_, hregular, hC0, hCq, hC, hCi, ?_⟩
    · intro x hx hc
      exact huniq x hx (by simpa only [mfderiv_neg, neg_eq_zero] using hc)
    · rw [data.modelDisk_image, hcomp.2]
      have heq := model_closure_strict_component (h := -H) hH.neg
        (neg_lt_neg hcomp.1) hregular
      simpa only [preimage, mem_Ici, mem_Iic, Pi.neg_apply, neg_le_neg_iff, H] using heq.symm
    · intro x hx
      change -H (C x) = -H q + ‖x‖^2
      have heq : H (C x) = H q - ‖x‖^2 := hform x hx
      rw [heq]
      ring




theorem physical_annulus_terminal_slices
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (d : OpenPartialHomeomorph E2 S2) (hds : closedBall 0 1 ⊆ d.source)
    {q : S2} (hq : q ∈ d '' closedBall 0 1) {b : Real} (hqb : h q < b)
    (hboundary : ∀ x ∈ sphere (0 : E2) 1, h (d x) = b)
    (hunique : ∀ x ∈ d '' closedBall 0 1,
      mfderiv (𝓡 2) 𝓘(Real, Real) h x = 0 → x = q)
    (C : OpenPartialHomeomorph E2 S2) {r : Real} (hr : 0 < r)
    (hCs : closedBall (0 : E2) r ⊆ C.source)
    (hform : ∀ x ∈ C.source, h (C x) = h q + ‖x‖ ^ 2)
    (hcb : h q + r ^ 2 < b)
    (F : OpenPartialHomeomorph (S1 × Real) S2) {δ : Real} (hδ : 0 < δ)
    (hheight : ∀ z t, t ∈ Ioo (h q + r ^ 2 - δ) (b + δ) → h (F (z, t)) = t)
    (hband : F '' (univ ×ˢ Icc (h q + r ^ 2) b) =
      (d '' closedBall 0 1) \ (C '' ball (0 : E2) r)) :
    range (fun z : S1 => F (z, b)) = d '' sphere (0 : E2) 1 ∧
      ∀ z t, t ∈ Ico (h q + r^2) b → F (z, t) ∈ d '' ball (0 : E2) 1 := by
  obtain ⟨_, _, _, hinterior⟩ :=
    height_bounds_on_disk_of_unique_critical hh d hds hq hqb hboundary hunique
  have hmem (z : S1) (t : Real) (ht : t ∈ Icc (h q + r^2) b) :
      F (z, t) ∈ d '' closedBall (0 : E2) 1 := by
    have hx := mem_image_of_mem F (show (z, t) ∈ univ ×ˢ Icc (h q + r^2) b from
      ⟨mem_univ _, ht⟩)
    rw [hband] at hx
    exact hx.1
  constructor
  · apply subset_antisymm
    · rintro _ ⟨z, rfl⟩
      obtain ⟨x, hx, hxe⟩ := hmem z b ⟨hcb.le, le_rfl⟩
      refine ⟨x, ?_, hxe⟩
      apply mem_sphere_zero_iff_norm.mpr
      apply le_antisymm (mem_closedBall_zero_iff.mp hx)
      by_contra hnot
      have hxb := mem_ball_zero_iff.mpr (lt_of_not_ge hnot)
      have hlt := hinterior _ (mem_image_of_mem d hxb)
      rw [hxe, hheight z b ⟨by linarith, by linarith⟩] at hlt
      exact lt_irrefl _ hlt
    · rintro y ⟨x, hx, rfl⟩
      have hnot : d x ∉ C '' ball (0 : E2) r := by
        rintro ⟨u, hu, hue⟩
        have hlt : ‖u‖^2 < r^2 := (sq_lt_sq₀ (norm_nonneg u) hr.le).mpr
          (mem_ball_zero_iff.mp hu)
        have heq := hform u (hCs (ball_subset_closedBall hu))
        rw [hue, hboundary x hx] at heq
        linarith
      have hdx : d x ∈ F '' (univ ×ˢ Icc (h q + r^2) b) := by
        rw [hband]
        exact ⟨mem_image_of_mem d (sphere_subset_closedBall hx), hnot⟩
      obtain ⟨⟨z, t⟩, ⟨_, ht⟩, hzt⟩ := hdx
      have htb : t = b := by
        have heq := hheight z t ⟨by linarith [ht.1], by linarith [ht.2]⟩
        rw [hzt, hboundary x hx] at heq
        exact heq.symm
      exact ⟨z, htb ▸ hzt⟩
  · intro z t ht
    obtain ⟨x, hx, hxe⟩ := hmem z t ⟨ht.1, ht.2.le⟩
    refine ⟨x, ?_, hxe⟩
    apply mem_ball_zero_iff.mpr
    apply lt_of_le_of_ne (mem_closedBall_zero_iff.mp hx)
    intro heq
    have hxb := mem_sphere_zero_iff_norm.mpr heq
    have hhx := hboundary x hxb
    rw [hxe, hheight z t ⟨by linarith [ht.1], by linarith [ht.2]⟩] at hhx
    exact ht.2.ne hhx



theorem exists_terminal_model_physical_annulus
    (data : TerminalSaddleData M P p e) (i : Fin 3) :
    let H : S2 → Real := fun q => inner Real (M.v : E3)
      (data.toTerminalSaddleGeometry.filledModel q)
    ∃ h : S2 → Real, ∃ b : Real, ∃ q : S2, ∃ C : OpenPartialHomeomorph E2 S2,
      ((h = H ∧ b = data.ends.lowerCut) ∨
        (h = -H ∧ b = -data.ends.upperCut)) ∧
      ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h ∧
      q ∈ data.modelDisk i '' closedBall (0 : E2) 1 ∧ h q < b ∧
      (∀ x ∈ sphere (0 : E2) 1, h (data.modelDisk i x) = b) ∧
      (∀ x ∈ data.modelDisk i '' closedBall (0 : E2) 1,
        mfderiv (𝓡 2) 𝓘(Real, Real) h x = 0 → x = q) ∧
      data.modelDisk i '' closedBall (0 : E2) 1 =
        closure (connectedComponentIn (h ⁻¹' Iio b) (data.modelSeed i)) ∧
      (∀ x, h x = b → mfderiv (𝓡 2) 𝓘(Real, Real) h x ≠ 0) ∧
      0 ∈ C.source ∧ C 0 = q ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target ∧
      (∀ x ∈ C.source, h (C x) = h q + ‖x‖^2) ∧
      ∃ R : Real, 0 < R ∧ h q + R^2 < b ∧ closedBall (0 : E2) R ⊆ C.source ∧
        ∀ r ∈ Ioc (0 : Real) R, ∃ δ : Real, 0 < δ ∧
          ∃ F : OpenPartialHomeomorph (S1 × Real) S2,
            F.source = univ ×ˢ Ioo (h q + r^2 - δ) (b + δ) ∧
            ContMDiffOn IP (𝓡 2) ∞ F F.source ∧
            ContMDiffOn (𝓡 2) IP ∞ F.symm F.target ∧
            (∀ z t, t ∈ Ioo (h q + r^2 - δ) (b + δ) → h (F (z, t)) = t) ∧
            range (fun z : S1 => F (z, h q + r^2)) = C '' sphere (0 : E2) r ∧
            F '' (univ ×ˢ Icc (h q + r^2) b) =
              (data.modelDisk i '' closedBall 0 1) \ (C '' ball (0 : E2) r) ∧
            data.modelDisk i '' closedBall (0 : E2) 1 =
              C '' closedBall (0 : E2) r ∪ F '' (univ ×ˢ Icc (h q + r^2) b) ∧
            range (fun z : S1 => F (z, b)) = data.modelDisk i '' sphere (0 : E2) 1 ∧
            ∀ z t, t ∈ Ioo (b - δ) b → F (z, t) ∈ data.modelDisk i '' ball (0 : E2) 1 := by
  obtain ⟨h, b, q, C, horient, hh, hq, hqb, hboundary, hunique, hcomponent,
      hregular, hC0, hCq, hC, hCi, hform⟩ := exists_terminal_model_oriented_morse_cap data i
  refine ⟨h, b, q, C, horient, hh, hq, hqb, hboundary, hunique, hcomponent,
    hregular, hC0, hCq, hC, hCi, hform, ?_⟩
  obtain ⟨R, hR, hRb, hRs, hfamily⟩ := exists_morse_disk_and_physical_annulus_cover hh
    (data.modelDisk i) (data.modelDisk_source i) hq hqb hboundary hunique
    (data.modelSeed i) hcomponent hregular C hC0 hCq hform
  refine ⟨R, hR, hRb, hRs, ?_⟩
  intro r hr
  obtain ⟨δ, hδ, F, hFs, hF, hFi, hheight, hbottom, hband, hcover⟩ := hfamily r hr
  have hcb : h q + r^2 < b := by
    have hsq := (sq_le_sq₀ hr.1.le hR.le).mpr hr.2
    linarith
  obtain ⟨htop, hnegative⟩ := physical_annulus_terminal_slices hh (data.modelDisk i)
    (data.modelDisk_source i) hq hqb hboundary hunique C hr.1
    ((closedBall_subset_closedBall hr.2).trans hRs) hform hcb F hδ hheight hband
  let ε := min δ (b - (h q + r^2))
  have hε : 0 < ε := lt_min hδ (sub_pos.mpr hcb)
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεgap : ε ≤ b - (h q + r^2) := min_le_right _ _
  let U : Set (S1 × Real) := univ ×ˢ Ioo (h q + r^2 - ε) (b + ε)
  have hUs : U ⊆ F.source := by
    rintro ⟨z, t⟩ ⟨_, ht⟩
    rw [hFs]
    exact ⟨mem_univ _, by linarith [ht.1], by linarith [ht.2]⟩
  let F' := F.restrOpen U (isOpen_univ.prod isOpen_Ioo)
  refine ⟨ε, hε, F', inter_eq_right.mpr hUs,
    hF.mono inter_subset_left, hFi.mono inter_subset_left, ?_, hbottom, hband, hcover, htop, ?_⟩
  · intro z t ht
    exact hheight z t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · intro z t ht
    exact hnegative z t ⟨by linarith [ht.1], ht.2⟩

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
