import PoincareConjecture.Proofs.M38.MonodromyProjection

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

variable (phi : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)

attribute [local instance] monodromyChartedSpace monodromy_isManifold

local notation "mq" => (Quotient.mk (monodromyOrbitRel phi) :
  monodromyPunctureOpen → MonodromyQuotient phi)

theorem monodromy_quotient_deck (n : ℤ) (x : monodromyPunctureOpen) :
    mq (monodromyDeck phi n x) = mq x :=
  (monodromy_quotient_eq_iff phi _ _).mpr ⟨n, rfl⟩

theorem monodromy_same_log_eq {x y : monodromyPunctureOpen}
    (hxy : mq x = mq y) (hlog : monodromyLogRadius x = monodromyLogRadius y) : x = y := by
  obtain ⟨n, hn⟩ := (monodromy_quotient_eq_iff phi x y).mp hxy
  have heq := congrArg monodromyLogRadius hn
  rw [monodromyDeck_logRadius] at heq
  have hnzero : n = 0 := Int.cast_eq_zero.mp (by linarith : (n : ℝ) = 0)
  simpa only [hnzero, monodromyDeck_zero] using hn.symm

noncomputable def monodromyNormalize (s : ℝ) (q : MonodromyQuotient phi) :
    monodromyPunctureOpen :=
  monodromyDeck phi (⌊s - monodromyLogRadius (monodromyRepresentative phi q)⌋)
    (monodromyRepresentative phi q)

theorem monodromyNormalize_quotient (s : ℝ) (q : MonodromyQuotient phi) :
    mq (monodromyNormalize phi s q) = q :=
  (monodromy_quotient_deck phi _ _).trans (monodromyRepresentative_spec phi q)

theorem monodromyNormalize_logRadius (s : ℝ) (q : MonodromyQuotient phi)
    (hq : monodromyProjection phi q = circlePeriodMap s) :
    monodromyLogRadius (monodromyNormalize phi s q) = s := by
  have he : circlePeriodMap (monodromyLogRadius (monodromyRepresentative phi q)) =
      monodromyProjection phi q :=
    congrArg (monodromyProjection phi) (monodromyRepresentative_spec phi q)
  obtain ⟨n, hn⟩ := (circlePeriodMap_eq_iff s
    (monodromyLogRadius (monodromyRepresentative phi q))).mp (hq.symm.trans he.symm)
  have hd : s - monodromyLogRadius (monodromyRepresentative phi q) = (n : ℝ) := by
    linarith
  rw [monodromyNormalize, monodromyDeck_logRadius, hd, Int.floor_intCast]
  linarith

theorem monodromyNormalize_eq {s : ℝ} {q : MonodromyQuotient phi}
    {x : monodromyPunctureOpen} (hx : mq x = q) (hlog : monodromyLogRadius x = s) :
    monodromyNormalize phi s q = x := by
  have hq : monodromyProjection phi q = circlePeriodMap s := by
    have he := congrArg (monodromyProjection phi) hx
    rw [monodromyProjection_mk, hlog] at he
    exact he.symm
  apply monodromy_same_log_eq phi ((monodromyNormalize_quotient phi s q).trans hx.symm)
  exact (monodromyNormalize_logRadius phi s q hq).trans hlog.symm

theorem monodromyNormalize_smooth {W : Set (MonodromyQuotient phi)}
    (hW : IsOpen W) {s : MonodromyQuotient phi → ℝ}
    (hs : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ s W)
    (hperiod : ∀ q ∈ W, monodromyProjection phi q = circlePeriodMap (s q)) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun q => monodromyNormalize phi (s q) q) W := by
  intro p hp
  let e := (monodromy_quotient_localHomeomorph phi).localInverseAt
    (monodromyRepresentative phi p)
  have he : p ∈ e.source := by
    rw [← monodromyRepresentative_spec phi p]
    exact (monodromy_quotient_localHomeomorph phi).apply_self_mem_localInverseAt_source
  let V : Set (MonodromyQuotient phi) := W ∩ e.source
  have hV : IsOpen V := hW.inter e.open_source
  have hpV : p ∈ V := ⟨hp, he⟩
  let d : MonodromyQuotient phi → ℝ := fun q => s q - monodromyLogRadius (e q)
  have hd : ContinuousAt d p :=
    (hs.contMDiffAt (hW.mem_nhds hp)).continuousAt.sub
      (monodromyLogRadius_smooth.continuous.continuousAt.comp
        (monodromy_chosen_sheet_contMDiffAt phi p).continuousAt)
  have hint (q : MonodromyQuotient phi) (hq : q ∈ V) : ∃ n : ℤ, d q = (n : ℝ) := by
    have heq : mq (e q) = q :=
      (monodromy_quotient_localHomeomorph phi).apply_localInverseAt_of_mem hq.2
    have heperiod : circlePeriodMap (monodromyLogRadius (e q)) =
        monodromyProjection phi q := congrArg (monodromyProjection phi) heq
    obtain ⟨n, hn⟩ := (circlePeriodMap_eq_iff (s q) (monodromyLogRadius (e q))).mp
      ((hperiod q hq.1).symm.trans heperiod.symm)
    exact ⟨n, by dsimp [d]; linarith⟩
  obtain ⟨n, hn⟩ := hint p hpV
  have hnear : d ⁻¹' Ioo ((n : ℝ) - 1 / 2) ((n : ℝ) + 1 / 2) ∈ 𝓝 p :=
    hd (isOpen_Ioo.mem_nhds (by rw [hn]; constructor <;> linarith))
  have hfixed : (fun q => monodromyNormalize phi (s q) q) =ᶠ[𝓝 p]
      (fun q => monodromyDeck phi n (e q)) := by
    filter_upwards [hV.mem_nhds hpV, hnear] with q hq hbound
    obtain ⟨m, hm⟩ := hint q hq
    change (n : ℝ) - 1 / 2 < d q ∧ d q < (n : ℝ) + 1 / 2 at hbound
    rw [hm] at hbound
    have hlo : n - 1 < m := by
      have hh : (n : ℝ) - 1 < (m : ℝ) := by linarith [hbound.1]
      exact_mod_cast hh
    have hhi : m < n + 1 := by
      have hh : (m : ℝ) < (n : ℝ) + 1 := by linarith [hbound.2]
      exact_mod_cast hh
    have hmn : m = n := by omega
    have heq : mq (e q) = q :=
      (monodromy_quotient_localHomeomorph phi).apply_localInverseAt_of_mem hq.2
    apply monodromyNormalize_eq phi ((monodromy_quotient_deck phi n (e q)).trans heq)
    rw [monodromyDeck_logRadius]
    dsimp [d] at hm
    rw [hmn] at hm
    linarith
  exact (((monodromyDeck_smooth phi n).contMDiffAt.comp p
    (monodromy_chosen_sheet_contMDiffAt phi p)).congr_of_eventuallyEq hfixed).contMDiffWithinAt

end PoincareConjecture.M38
