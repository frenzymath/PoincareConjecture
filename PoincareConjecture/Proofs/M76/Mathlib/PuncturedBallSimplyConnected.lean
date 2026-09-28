import PoincareConjecture.Proofs.M76.Mathlib.PuncturedSpaceSimplyConnected
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph











set_option autoImplicit false

open Set Metric

namespace OpenPartialHomeomorph




theorem isSimplyConnected_image_of_subset_source
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {s : Set X} (hsub : s ⊆ e.source)
    (hs : IsSimplyConnected s) : IsSimplyConnected (e '' s) := by
  let : SimplyConnectedSpace s := hs
  exact (e.homeomorphOfImageSubsetSource hsub rfl).symm.toHomotopyEquiv.simplyConnectedSpace



theorem image_sdiff_singleton_of_subset_source
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {s : Set X} (hsub : s ⊆ e.source)
    {x : X} (hx : x ∈ e.source) :
    e '' (s \ {x}) = (e '' s) \ {e x} := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨⟨z, hz.1, rfl⟩, ?_⟩
    intro heq
    exact hz.2 (e.injOn (hsub hz.1) hx heq)
  · rintro ⟨⟨z, hz, rfl⟩, hne⟩
    refine ⟨z, ⟨hz, ?_⟩, rfl⟩
    intro hzx
    exact hne (congrArg e hzx)

end OpenPartialHomeomorph





theorem isSimplyConnected_ball_sdiff_center_of_two_lt_finrank
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : 2 < Module.finrank ℝ E)
    (c : E) {r : ℝ} (hr : 0 < r) : IsSimplyConnected (ball c r \ {c}) := by
  let e : OpenPartialHomeomorph E E := OpenPartialHomeomorph.univBall c r
  have hes : e.source = univ := OpenPartialHomeomorph.univBall_source c r
  have het : e.target = ball c r := OpenPartialHomeomorph.univBall_target c hr
  have he0 : e 0 = c := OpenPartialHomeomorph.univBall_apply_zero c r
  have himage : e '' ({0}ᶜ : Set E) = ball c r \ {c} := by
    rw [show ({0}ᶜ : Set E) = univ \ {0} by
      ext x
      exact ⟨fun hx => ⟨mem_univ x, hx⟩, And.right⟩]
    rw [e.image_sdiff_singleton_of_subset_source (hes.symm.subset) (by rw [hes]; trivial)]
    rw [← hes, e.image_source_eq_target, het, he0]
  rw [← himage]
  exact e.isSimplyConnected_image_of_subset_source
    (fun _ _ => hes.symm ▸ mem_univ _) (isSimplyConnected_compl_zero_of_two_lt_finrank hdim)
