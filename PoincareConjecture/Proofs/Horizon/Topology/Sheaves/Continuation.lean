import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Sheaves.EtaleSpace
import Mathlib.Topology.Sheaves.LocalPredicate

noncomputable section

open CategoryTheory TopologicalSpace Opposite Filter
open scoped Topology

namespace Poincare.Topology

universe u v

variable {X : TopCat.{max u v}} {T : X → Type v} (P : TopCat.LocalPredicate T)

theorem exists_globalSection_of_continuous_etaleSection
    (l : C(X, (TopCat.subsheafToTypes P).presheaf.EtaleSpace))
    (hl : ∀ x, (l x).base = x) :
    ∃ f : (TopCat.subsheafToTypes P).presheaf.obj (op ⊤),
      ∀ x, l x = ⟨x, (TopCat.subsheafToTypes P).presheaf.germ ⊤ x (by trivial) f⟩ := by
  let F := (TopCat.subsheafToTypes P).presheaf
  have hsection (x : X) : ∃ a : F.stalk x, l x = ⟨x, a⟩ := by
    generalize he : l x = z
    have hz : z.base = x := he ▸ hl x
    rcases z with ⟨y, a⟩
    dsimp at hz
    subst y
    exact ⟨a, rfl⟩
  choose s hs using hsection
  have hcont : Continuous (fun x => (⟨x, s x⟩ : F.EtaleSpace)) := by
    simpa only [← hs] using l.continuous

  have hvalue (x : X) : ∃ a : T x, ∀ (U : Opens X) (hx : x ∈ U)
      (f : F.obj (op U)), F.germ U x hx f = s x → f.1 ⟨x, hx⟩ = a := by
    obtain ⟨V, hxV, f, hf⟩ := F.exists_germ_eq (s x)
    refine ⟨f.1 ⟨x, hxV⟩, ?_⟩
    intro U hxU g hg
    obtain ⟨W, hxW, iWU, iWV, hgf⟩ := F.germ_eq x hxU hxV g f (hg.trans hf.symm)
    exact congrArg (fun k : F.obj (op W) => k.1 ⟨x, hxW⟩) hgf
  choose a ha using hvalue
  have hlocal (x : X) : ∃ (U : Opens X) (hxU : x ∈ U)
      (f : F.obj (op U)), ∀ y (hy : y ∈ U), s y = F.germ U y hy f := by
    obtain ⟨V, hxV, f, hf⟩ :=
      TopCat.Presheaf.EtaleSpace.exists_section_of_tendsto
        (show ContinuousAt (fun y => (⟨y, s y⟩ : F.EtaleSpace)) x from hcont.continuousAt)
    obtain ⟨W, hW, hWo, hxW⟩ := mem_nhds_iff.mp hf
    let U : Opens X := V ⊓ ⟨W, hWo⟩
    refine ⟨U, ⟨hxV, hxW⟩, F.map (Opens.infLELeft V ⟨W, hWo⟩).op f, ?_⟩
    intro y hy
    obtain ⟨hyV, hfy⟩ := hW hy.2
    rw [F.germ_res_apply]
    exact hfy
  let f (x : (⊤ : Opens X)) : T x := a x
  have hf : P.pred f := by
    apply P.locality
    intro x
    obtain ⟨U, hxU, g, hg⟩ := hlocal x
    refine ⟨U, hxU, homOfLE le_top, ?_⟩
    convert g.property using 1
    funext y
    exact (ha y U y.property g (hg y y.property).symm).symm
  refine ⟨⟨f, hf⟩, ?_⟩
  intro x
  rw [hs]
  congr 1
  obtain ⟨U, hxU, g, hg⟩ := hlocal x
  rw [hg x hxU]
  symm
  apply F.germ_ext U hxU (homOfLE le_top) (𝟙 U)
  apply Subtype.ext
  funext y
  exact (ha y U y.property g (hg y y.property).symm).symm

theorem exists_globalSection_of_locally_bijective_germ
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (hP : ∀ x, ∃ (U : Opens X), x ∈ U ∧ ∀ y (hy : y ∈ U),
      Function.Bijective ((TopCat.subsheafToTypes P).presheaf.germ U y hy))
    (x₀ : X) (g₀ : (TopCat.subsheafToTypes P).presheaf.stalk x₀) :
    ∃ f : (TopCat.subsheafToTypes P).presheaf.obj (op ⊤),
      (TopCat.subsheafToTypes P).presheaf.germ ⊤ x₀ (by trivial) f = g₀ := by
  let F := (TopCat.subsheafToTypes P).presheaf
  have hcov := TopCat.Presheaf.EtaleSpace.isCoveringMap_base hP
  obtain ⟨l, ⟨hl₀, hl⟩, _⟩ :=
    hcov.existsUnique_continuousMap_lifts (ContinuousMap.id X) x₀ ⟨x₀, g₀⟩ rfl
  obtain ⟨f, hf⟩ := exists_globalSection_of_continuous_etaleSection P l
    (fun x => congrFun hl x)
  refine ⟨f, ?_⟩
  have heq := (hf x₀).symm.trans hl₀
  cases heq
  rfl

end Poincare.Topology
