import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.RegularLevel.ComponentBand

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

private instance : ConnectedSpace S1 :=
  isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by simp [← Module.finrank_eq_rank, E2]) (0 : E2) zero_le_one)

theorem exists_smooth_regular_band_component_through_point
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {a b : Real} (hab : a < b)
    (hregular : ∀ p : S2, h p ∈ Icc a b →
      mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    (p : S2) (hp : h p ∈ Icc a b) :
    ∃ δ : Real, 0 < δ ∧ ∃ F : OpenPartialHomeomorph (S1 × Real) S2,
      F.source = univ ×ˢ Ioo (a - δ) (b + δ) ∧
      ContMDiffOn Iprod (𝓡 2) ∞ F F.source ∧
      ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target ∧
      (∀ q t, t ∈ Ioo (a - δ) (b + δ) → h (F (q, t)) = t) ∧
      F '' (univ ×ˢ Icc a b) = connectedComponentIn (h ⁻¹' Icc a b) p ∧
      p ∈ F '' (univ ×ˢ Icc a b) := by
  have hbottom : ∃ y : S2, h y = a ∧
      p ∈ connectedComponentIn (h ⁻¹' Icc a b) y := by
    by_cases hpa : h p = a
    · exact ⟨p, hpa, mem_connectedComponentIn hp⟩
    have hap : a < h p := lt_of_le_of_ne hp.1 (Ne.symm hpa)
    have hnreg : ∀ q : S2, -h q ∈ Icc (-h p) (-a) →
        mfderiv (𝓡 2) 𝓘(Real, Real) (fun y => -h y) q ≠ 0 := by
      intro q hq hn
      apply hregular q (show h q ∈ Icc a b from
        ⟨by linarith [hq.2], by linarith [hq.1, hp.2]⟩)
      change mfderiv (𝓡 2) 𝓘(Real, Real) (-h) q = 0 at hn
      simpa only [mfderiv_neg, neg_eq_zero] using hn
    obtain ⟨ε, hε, G, hGs, hG, _, hheight, hstart, _⟩ :=
      exists_smooth_regular_band_component_of_smooth hh.neg
        (neg_lt_neg hap) hnreg p rfl
    obtain ⟨q₀⟩ := (inferInstance : Nonempty S1)
    let K := G '' (univ ×ˢ Icc (-h p) (-a))
    have hsub : univ ×ˢ Icc (-h p) (-a) ⊆ G.source := by
      rintro ⟨q, t⟩ ⟨_, ht⟩
      rw [hGs]
      exact ⟨mem_univ _, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
    have hK : IsPreconnected K :=
      (isPreconnected_univ.prod isPreconnected_Icc).image _
        (G.continuousOn.mono hsub)
    have hKband : K ⊆ h ⁻¹' Icc a b := by
      rintro z ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      have hqt := hheight q t ⟨by linarith [ht.1], by linarith [ht.2]⟩
      change -h (G (q, t)) = t at hqt
      constructor <;> linarith [ht.1, ht.2, hp.2]
    have hpK : p ∈ K := by
      have hpstart : p ∈ range (fun q : S1 => G (q, -h p)) := by
        rw [hstart]
        exact mem_connectedComponentIn rfl
      obtain ⟨q, hqp⟩ := hpstart
      exact ⟨(q, -h p), ⟨mem_univ _, le_rfl, (neg_le_neg hp.1)⟩, hqp⟩
    let y := G (q₀, -a)
    have hyK : y ∈ K := ⟨(q₀, -a), ⟨mem_univ _, neg_le_neg hp.1, le_rfl⟩, rfl⟩
    refine ⟨y, ?_, hK.subset_connectedComponentIn hyK hKband hpK⟩
    have hy := hheight q₀ (-a) ⟨by linarith, by linarith⟩
    change -h y = -a at hy
    linarith
  obtain ⟨y, hy, hpy⟩ := hbottom
  obtain ⟨δ, hδ, F, hFs, hF, hFi, hheight, _, hband⟩ :=
    exists_smooth_regular_band_component_of_smooth hh hab hregular y hy
  have hbandp : F '' (univ ×ˢ Icc a b) =
      connectedComponentIn (h ⁻¹' Icc a b) p :=
    hband.trans (connectedComponentIn_eq hpy)
  exact ⟨δ, hδ, F, hFs, hF, hFi, hheight, hbandp,
    hbandp ▸ mem_connectedComponentIn hp⟩

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
