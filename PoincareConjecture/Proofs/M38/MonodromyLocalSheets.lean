import PoincareConjecture.Proofs.M38.MonodromyQuotient

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

variable (phi : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)

theorem monodromyLift_eventually_deck
    {g : monodromyPunctureOpen → monodromyPunctureOpen}
    {W : Set monodromyPunctureOpen} (hW : IsOpen W) (hg : ContinuousOn g W)
    (hfiber : ∀ x ∈ W,
      (Quotient.mk (monodromyOrbitRel phi) (g x) : MonodromyQuotient phi) =
        Quotient.mk (monodromyOrbitRel phi) x)
    {x : monodromyPunctureOpen} (hx : x ∈ W) :
    ∃ n : ℤ, g =ᶠ[𝓝 x] monodromyDeck phi n := by
  obtain ⟨n, hn⟩ := (monodromy_quotient_eq_iff phi (g x) x).mp (hfiber x hx)
  let f : monodromyPunctureOpen → ℝ :=
    fun y => monodromyLogRadius (g y) - monodromyLogRadius y
  have hcont : ContinuousAt g x := (hg x hx).continuousAt (hW.mem_nhds hx)
  have hc : ContinuousAt f x :=
    (monodromyLogRadius_smooth.continuous.continuousAt.comp hcont).sub
      monodromyLogRadius_smooth.continuous.continuousAt
  have hfn : f x = (n : ℝ) := by
    dsimp [f]
    rw [← hn, monodromyDeck_logRadius]
    ring
  have hnear : f ⁻¹' Ioo ((n : ℝ) - 1 / 2) ((n : ℝ) + 1 / 2) ∈ 𝓝 x :=
    hc (isOpen_Ioo.mem_nhds (by rw [hfn]; constructor <;> linarith))
  refine ⟨n, ?_⟩
  filter_upwards [hW.mem_nhds hx, hnear] with y hy hfy
  obtain ⟨m, hm⟩ := (monodromy_quotient_eq_iff phi (g y) y).mp (hfiber y hy)
  have hfm : f y = (m : ℝ) := by
    dsimp [f]
    rw [← hm, monodromyDeck_logRadius]
    ring
  change (n : ℝ) - 1 / 2 < f y ∧ f y < (n : ℝ) + 1 / 2 at hfy
  rw [hfm] at hfy
  have hlo : n - 1 < m := by
    have hh : (n : ℝ) - 1 < (m : ℝ) := by linarith [hfy.1]
    exact_mod_cast hh
  have hhi : m < n + 1 := by
    have hh : (m : ℝ) < (n : ℝ) + 1 := by linarith [hfy.2]
    exact_mod_cast hh
  have hmn : m = n := by omega
  simpa only [hmn] using hm.symm

theorem monodromyLift_contMDiffOn
    {g : monodromyPunctureOpen → monodromyPunctureOpen}
    {W : Set monodromyPunctureOpen} (hW : IsOpen W) (hg : ContinuousOn g W)
    (hfiber : ∀ x ∈ W,
      (Quotient.mk (monodromyOrbitRel phi) (g x) : MonodromyQuotient phi) =
        Quotient.mk (monodromyOrbitRel phi) x) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ g W := by
  intro x hx
  obtain ⟨n, hn⟩ := monodromyLift_eventually_deck phi hW hg hfiber hx
  exact ((monodromyDeck_smooth phi n x).congr_of_eventuallyEq hn).contMDiffWithinAt

theorem monodromy_sheet_transition_smooth (a : monodromyPunctureOpen) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞
      ((monodromy_quotient_localHomeomorph phi).localInverseAt a ∘
        (Quotient.mk (monodromyOrbitRel phi) :
          monodromyPunctureOpen → MonodromyQuotient phi))
      ((Quotient.mk (monodromyOrbitRel phi) :
          monodromyPunctureOpen → MonodromyQuotient phi) ⁻¹'
        ((monodromy_quotient_localHomeomorph phi).localInverseAt a).source) := by
  let e := (monodromy_quotient_localHomeomorph phi).localInverseAt a
  have hc := (monodromy_open_quotient phi).continuous
  apply monodromyLift_contMDiffOn phi (e.open_source.preimage hc)
    (e.continuousOn.comp hc.continuousOn (fun _ hx => hx))
  intro x hx
  exact (monodromy_quotient_localHomeomorph phi).apply_localInverseAt_of_mem hx

end PoincareConjecture.M38
