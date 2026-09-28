import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Extremum.DiskSublevels



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1




theorem exists_boundary_band_cover_of_unique_critical_disk
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (d : OpenPartialHomeomorph E2 S2) (hds : closedBall 0 1 ⊆ d.source)
    {p : S2} (hp : p ∈ d '' closedBall 0 1) {b : Real} (hpb : h p < b)
    (hboundary : ∀ x ∈ sphere (0 : E2) 1, h (d x) = b)
    (hunique : ∀ x ∈ d '' closedBall 0 1,
      mfderiv (𝓡 2) 𝓘(Real, Real) h x = 0 → x = p)
    {ε : Real} (hε : 0 < ε) (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hTs : T.source = univ ×ˢ Ioo (-ε) ε)
    (hTh : ∀ q t, t ∈ Ioo (-ε) ε → h (T (q, t)) = b + t)
    (hTc : range (fun q : S1 => T (q, 0)) = d '' sphere (0 : E2) 1)
    (hTneg : ∀ q : S1, ∀ t ∈ Ioo (-ε) 0, T (q, t) ∈ d '' ball 0 1) :
    ∃ δ : Real, 0 < δ ∧ δ < ε ∧
      ∀ t ∈ Icc (-δ) 0,
        (d '' closedBall 0 1) ∩ h ⁻¹' {b + t} = range (fun q : S1 => T (q, t)) := by
  let K := d '' closedBall (0 : E2) 1
  have hK : IsCompact K :=
    (isCompact_closedBall 0 1).image_of_continuousOn (d.continuousOn.mono hds)
  obtain ⟨_, _, _, hlt⟩ :=
    height_bounds_on_disk_of_unique_critical hh d hds hp hpb hboundary hunique
  have hfront : frontier K ⊆ T.target := by
    rw [← d.image_sphere_eq_frontier hds rfl, ← hTc]
    rintro _ ⟨q, rfl⟩
    apply T.map_source
    rw [hTs]
    exact ⟨mem_univ _, ⟨neg_lt_zero.mpr hε, hε⟩⟩
  have hlow (x : S2) (hx : x ∈ K \ T.target) : h x < b := by
    apply hlt
    rw [d.image_ball_eq_interior hds rfl]
    exact (mem_interior_iff_notMem_frontier hx.1).mpr (fun hxf => hx.2 (hfront hxf))
  have hgap : ∃ η : Real, 0 < η ∧ ∀ x ∈ K, b - η ≤ h x → x ∈ T.target := by
    by_cases hne : (K \ T.target).Nonempty
    · obtain ⟨q, hq, hqmax⟩ := (hK.diff T.open_target).exists_isMaxOn hne hh.continuous.continuousOn
      have hqb := hlow q hq
      refine ⟨(b - h q) / 2, by linarith, ?_⟩
      intro x hx hxh
      by_contra hxt
      have : h x ≤ h q := hqmax ⟨hx, hxt⟩
      linarith
    · refine ⟨1, zero_lt_one, ?_⟩
      intro x hx _
      by_contra hxt
      exact hne ⟨x, hx, hxt⟩
  obtain ⟨η, hη, hηT⟩ := hgap
  let δ := min η ε / 2
  have hδ : 0 < δ := half_pos (lt_min hη hε)
  have hδε : δ < ε := by dsimp [δ]; linarith [min_le_right η ε]
  have hδη : δ ≤ η := by dsimp [δ]; linarith [min_le_left η ε]
  refine ⟨δ, hδ, hδε, ?_⟩
  intro t ht
  have htε : t ∈ Ioo (-ε) ε := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  ext x
  constructor
  · rintro ⟨hx, hxh⟩
    change h x = b + t at hxh
    have hxt := hηT x hx (by linarith [ht.1])
    have hxsource := T.map_target hxt
    rw [hTs] at hxsource
    have hhx := hTh (T.symm x).1 (T.symm x).2 hxsource.2
    rw [T.right_inv hxt] at hhx
    have htime : (T.symm x).2 = t := by linarith
    refine ⟨(T.symm x).1, ?_⟩
    rw [← htime]
    exact T.right_inv hxt
  · rintro ⟨q, rfl⟩
    refine ⟨?_, hTh q t htε⟩
    rcases lt_or_eq_of_le ht.2 with htn | rfl
    · exact image_mono ball_subset_closedBall (hTneg q t ⟨htε.1, htn⟩)
    · exact image_mono sphere_subset_closedBall (hTc ▸ mem_range_self q)

end Poincare.Manifold.Schoenflies
