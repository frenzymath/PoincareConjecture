import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.BallImages
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Caps



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1

private theorem compact_region_height_bounds
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {K : Set S2} (hK : IsCompact K) {p : S2} (hp : p ∈ K) {b : Real}
    (hpb : h p < b) (hboundary : ∀ x ∈ frontier K, h x = b)
    (hunique : ∀ x ∈ K, mfderiv (𝓡 2) 𝓘(Real, Real) h x = 0 → x = p) :
    IsLocalMin h p ∧
      (∀ x ∈ K, h p ≤ h x ∧ h x ≤ b) ∧
      (∀ x ∈ K, x ≠ p → h p < h x) ∧
      ∀ x ∈ interior K, h x < b := by
  have hinterior (x : S2) (hx : x ∈ K) (hxb : h x ≠ b) : x ∈ interior K :=
    (mem_interior_iff_notMem_frontier hx).mpr (fun hxf => hxb (hboundary x hxf))
  obtain ⟨q, hq, hqmin⟩ := hK.exists_isMinOn ⟨p, hp⟩ hh.continuous.continuousOn
  have hqb : h q < b := (hqmin hp).trans_lt hpb
  have hqp : q = p := hunique q hq
    (Poincare.Geometry.Manifold.mfderiv_eq_zero_of_isLocalMin hh
      (hqmin.isLocalMin (mem_interior_iff_mem_nhds.mp (hinterior q hq hqb.ne))))
  subst q
  have hpmin : IsLocalMin h p :=
    hqmin.isLocalMin (mem_interior_iff_mem_nhds.mp (hinterior p hp hpb.ne))
  have hmaxcrit {x : S2} (hx : IsLocalMax h x) :
      mfderiv (𝓡 2) 𝓘(Real, Real) h x = 0 := by
    have hn := Poincare.Geometry.Manifold.mfderiv_eq_zero_of_isLocalMin hh.neg hx.neg
    change mfderiv (𝓡 2) 𝓘(Real, Real) (-h) x = 0 at hn
    simpa only [mfderiv_neg, neg_eq_zero] using hn
  obtain ⟨q, hq, hqmax⟩ := hK.exists_isMaxOn ⟨p, hp⟩ hh.continuous.continuousOn
  have hqle : h q ≤ b := by
    by_contra hqle
    have hqb : b < h q := lt_of_not_ge hqle
    have hqp : q = p := hunique q hq
      (hmaxcrit (hqmax.isLocalMax
        (mem_interior_iff_mem_nhds.mp (hinterior q hq hqb.ne'))))
    subst q
    linarith
  have hle (x : S2) (hx : x ∈ K) : h x ≤ b := (hqmax hx).trans hqle
  refine ⟨hpmin, fun x hx => ⟨hqmin hx, hle x hx⟩, ?_, ?_⟩
  · intro x hx hxp
    apply lt_of_le_of_ne (hqmin hx)
    intro heq
    have hxMin : IsMinOn h K x := by
      intro y hy
      rw [← heq]
      exact hqmin hy
    exact hxp (hunique x hx (Poincare.Geometry.Manifold.mfderiv_eq_zero_of_isLocalMin hh
      (hxMin.isLocalMin (mem_interior_iff_mem_nhds.mp
        (hinterior x hx (by rw [← heq]; exact hpb.ne))))))
  · intro x hx
    apply lt_of_le_of_ne (hle x (interior_subset hx))
    intro hxb
    have hxMax : IsMaxOn h K x := by intro y hy; rw [hxb]; exact hle y hy
    have hxp := hunique x (interior_subset hx)
      (hmaxcrit (hxMax.isLocalMax (mem_interior_iff_mem_nhds.mp hx)))
    subst x
    exact hpb.ne hxb




theorem height_bounds_on_disk_of_unique_critical
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (d : OpenPartialHomeomorph E2 S2) (hds : closedBall 0 1 ⊆ d.source)
    {p : S2} (hp : p ∈ d '' closedBall 0 1) {b : Real} (hpb : h p < b)
    (hboundary : ∀ x ∈ sphere (0 : E2) 1, h (d x) = b)
    (hunique : ∀ x ∈ d '' closedBall 0 1,
      mfderiv (𝓡 2) 𝓘(Real, Real) h x = 0 → x = p) :
    IsLocalMin h p ∧
      (∀ x ∈ d '' closedBall 0 1, h p ≤ h x ∧ h x ≤ b) ∧
      (∀ x ∈ d '' closedBall 0 1, x ≠ p → h p < h x) ∧
      ∀ x ∈ d '' ball 0 1, h x < b := by
  have hK : IsCompact (d '' closedBall 0 1) :=
    (isCompact_closedBall 0 1).image_of_continuousOn (d.continuousOn.mono hds)
  have hfront : ∀ x ∈ frontier (d '' closedBall 0 1), h x = b := by
    rw [← d.image_sphere_eq_frontier hds rfl]
    rintro _ ⟨x, hx, rfl⟩
    exact hboundary x hx
  obtain ⟨hmin, hbounds, hstrict, hinterior⟩ :=
    compact_region_height_bounds hh hK hp hpb hfront hunique
  exact ⟨hmin, hbounds, hstrict, by simpa only [d.image_ball_eq_interior hds rfl] using hinterior⟩

private theorem exists_small_sublevel_subset_neighborhood
    {h : S2 → Real} (hh : Continuous h) {K : Set S2} (hK : IsCompact K)
    {p : S2} (hstrict : ∀ x ∈ K, x ≠ p → h p < h x)
    {U : Set S2} (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ δ : Real, 0 < δ ∧ ∀ x ∈ K, h x ≤ h p + δ → x ∈ U := by
  by_cases hne : (K \ U).Nonempty
  · obtain ⟨q, hq, hqmin⟩ := (hK.diff hU).exists_isMinOn hne hh.continuousOn
    have hqp : q ≠ p := by intro heq; exact hq.2 (heq ▸ hpU)
    have hgap := hstrict q hq.1 hqp
    refine ⟨(h q - h p) / 2, by linarith, ?_⟩
    intro x hx hxl
    by_contra hxU
    have : h q ≤ h x := hqmin ⟨hx, hxU⟩
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx _
    by_contra hxU
    exact hne ⟨x, hx, hxU⟩



theorem exists_exact_morse_sublevels_on_compact_disk
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (d : OpenPartialHomeomorph E2 S2) (hds : closedBall 0 1 ⊆ d.source)
    {p : S2} (hp : p ∈ d '' closedBall 0 1) {b : Real} (hpb : h p < b)
    (hboundary : ∀ x ∈ sphere (0 : E2) 1, h (d x) = b)
    (hunique : ∀ x ∈ d '' closedBall 0 1,
      mfderiv (𝓡 2) 𝓘(Real, Real) h x = 0 → x = p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (hform : ∀ x ∈ e.source, h (e x) = h p + ‖x‖ ^ 2) :
    ∃ R : Real, 0 < R ∧ h p + R ^ 2 < b ∧
      closedBall (0 : E2) R ⊆ e.source ∧
      e '' closedBall 0 R ⊆ d '' ball 0 1 ∧
      ∀ r ∈ Ioc (0 : Real) R,
        e '' closedBall 0 r = (d '' closedBall 0 1) ∩ h ⁻¹' Iic (h p + r ^ 2) ∧
        e '' ball 0 r = (d '' closedBall 0 1) ∩ h ⁻¹' Iio (h p + r ^ 2) ∧
        e '' sphere 0 r = (d '' closedBall 0 1) ∩ h ⁻¹' {h p + r ^ 2} := by
  let K := d '' closedBall (0 : E2) 1
  have hK : IsCompact K :=
    (isCompact_closedBall 0 1).image_of_continuousOn (d.continuousOn.mono hds)
  obtain ⟨_, hbounds, hstrict, _⟩ :=
    height_bounds_on_disk_of_unique_critical hh d hds hp hpb hboundary hunique
  have hpint : p ∈ interior K := by
    apply (mem_interior_iff_notMem_frontier hp).mpr
    rw [← d.image_sphere_eq_frontier hds rfl]
    rintro ⟨x, hx, hxp⟩
    exact hpb.ne (hxp ▸ hboundary x hx)
  have hcont := e.continuousOn.continuousAt (e.open_source.mem_nhds he0)
  have htarget := hcont.preimage_mem_nhds (isOpen_interior.mem_nhds
    (show e 0 ∈ interior K by rw [hep]; exact hpint))
  obtain ⟨R₀, hR₀, hR₀s⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem (e.open_source.mem_nhds he0) htarget)
  have hR₀source : closedBall (0 : E2) R₀ ⊆ e.source := fun x hx => (hR₀s hx).1
  let U := e '' ball (0 : E2) R₀
  have hU : IsOpen U := e.isOpen_image_of_subset_source isOpen_ball
    (ball_subset_closedBall.trans hR₀source)
  have hpU : p ∈ U := ⟨0, mem_ball_self hR₀, hep⟩
  obtain ⟨δ, hδ, hδU⟩ := exists_small_sublevel_subset_neighborhood hh.continuous hK hstrict hU hpU
  let R := min R₀ (min (Real.sqrt δ) (Real.sqrt (b - h p))) / 2
  have hR : 0 < R := half_pos (lt_min hR₀ (lt_min
    (Real.sqrt_pos.mpr hδ) (Real.sqrt_pos.mpr (sub_pos.mpr hpb))))
  have hRR₀ : R < R₀ := by dsimp [R]; linarith [min_le_left R₀ (min (Real.sqrt δ) (Real.sqrt (b - h p)))]
  have hRδ : R ^ 2 < δ := by
    have hle : R ≤ Real.sqrt δ / 2 := by
      dsimp [R]
      linarith [(min_le_right R₀ (min (Real.sqrt δ) (Real.sqrt (b - h p)))).trans
        (min_le_left (Real.sqrt δ) (Real.sqrt (b - h p)))]
    nlinarith [Real.sq_sqrt hδ.le, Real.sqrt_nonneg δ]
  have hRb : h p + R ^ 2 < b := by
    have hle : R ≤ Real.sqrt (b - h p) / 2 := by
      dsimp [R]
      linarith [(min_le_right R₀ (min (Real.sqrt δ) (Real.sqrt (b - h p)))).trans
        (min_le_right (Real.sqrt δ) (Real.sqrt (b - h p)))]
    nlinarith [Real.sq_sqrt (sub_pos.mpr hpb).le, Real.sqrt_nonneg (b - h p)]
  have hRs : closedBall (0 : E2) R ⊆ e.source :=
    (closedBall_subset_closedBall hRR₀.le).trans hR₀source
  have hRK : e '' closedBall (0 : E2) R ⊆ interior K := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hR₀s (closedBall_subset_closedBall hRR₀.le hx)).2
  refine ⟨R, hR, hRb, hRs, ?_, ?_⟩
  · simpa only [d.image_ball_eq_interior hds rfl] using hRK
  · intro r hr
    have hrs : closedBall (0 : E2) r ⊆ e.source :=
      (closedBall_subset_closedBall hr.2).trans hRs
    have hrK : e '' closedBall (0 : E2) r ⊆ K :=
      (image_mono (closedBall_subset_closedBall hr.2)).trans (hRK.trans interior_subset)
    have hsmall (x : S2) (hx : x ∈ K) (hhx : h x ≤ h p + r ^ 2) : x ∈ e.target := by
      have hrδ : r ^ 2 ≤ δ :=
        ((sq_le_sq₀ hr.1.le hR.le).mpr hr.2).trans hRδ.le
      obtain ⟨y, hy, rfl⟩ := hδU x hx (by linarith)
      exact e.map_source (hR₀source (ball_subset_closedBall hy))
    have hsqle (x : E2) : ‖x‖ ^ 2 ≤ r ^ 2 ↔ ‖x‖ ≤ r :=
      sq_le_sq₀ (norm_nonneg x) hr.1.le
    have hsqlt (x : E2) : ‖x‖ ^ 2 < r ^ 2 ↔ ‖x‖ < r :=
      sq_lt_sq₀ (norm_nonneg x) hr.1.le
    have hsqeq (x : E2) : ‖x‖ ^ 2 = r ^ 2 ↔ ‖x‖ = r :=
      sq_eq_sq₀ (norm_nonneg x) hr.1.le
    refine ⟨?_, ?_, ?_⟩
    · ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨hrK ⟨y, hy, rfl⟩, ?_⟩
        simpa only [mem_preimage, mem_Iic, hform y (hrs hy), add_le_add_iff_left,
          hsqle, mem_closedBall_zero_iff] using hy
      · rintro ⟨hx, hhx⟩
        change h x ≤ h p + r ^ 2 at hhx
        have hxt := hsmall x hx hhx
        refine ⟨e.symm x, ?_, e.right_inv hxt⟩
        have hheight := hform (e.symm x) (e.map_target hxt)
        rw [e.right_inv hxt] at hheight
        exact mem_closedBall_zero_iff.mpr ((hsqle _).mp (by linarith))
    · ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨hrK ⟨y, ball_subset_closedBall hy, rfl⟩, ?_⟩
        simpa only [mem_preimage, mem_Iio, hform y (hrs (ball_subset_closedBall hy)),
          add_lt_add_iff_left, hsqlt, mem_ball_zero_iff] using hy
      · rintro ⟨hx, hhx⟩
        change h x < h p + r ^ 2 at hhx
        have hxt := hsmall x hx (le_of_lt hhx)
        refine ⟨e.symm x, ?_, e.right_inv hxt⟩
        have hheight := hform (e.symm x) (e.map_target hxt)
        rw [e.right_inv hxt] at hheight
        exact mem_ball_zero_iff.mpr ((hsqlt _).mp (by linarith))
    · ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨hrK ⟨y, sphere_subset_closedBall hy, rfl⟩, ?_⟩
        simpa only [mem_preimage, mem_singleton_iff, hform y (hrs (sphere_subset_closedBall hy)),
          add_right_inj, hsqeq, mem_sphere_zero_iff_norm] using hy
      · rintro ⟨hx, hhx⟩
        change h x = h p + r ^ 2 at hhx
        have hxt := hsmall x hx (le_of_eq hhx)
        refine ⟨e.symm x, ?_, e.right_inv hxt⟩
        have hheight := hform (e.symm x) (e.map_target hxt)
        rw [e.right_inv hxt] at hheight
        exact mem_sphere_zero_iff_norm.mpr ((hsqeq _).mp (by linarith))

end Poincare.Manifold.Schoenflies
