import PoincareConjecture.Proofs.M03.Existence.DeTurckEndpointCalculusNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckJetCoordinatesNative









set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture.DeTurckJetProlongationNative

open DeTurckJetCoordinatesNative DeTurckEndpointCalculusNative

variable {d : ℕ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

local notation "P" => Fin d → ℝ
local notation "Jet" k:max => (WordIndex (Fin d) k → Z)

def finiteJet (k : ℕ) (u : List (Fin d) → Z) : Jet k := fun w => u (List.ofFn w.2)

def restrictJet (k : ℕ) : Jet (k + 1) →L[ℝ] Jet k :=
  ContinuousLinearMap.pi fun w => ContinuousLinearMap.proj
    (wordIndex (List.ofFn w.2) (by simp only [List.length_ofFn]; omega))

def shiftJet (k : ℕ) (i : Fin d) : Jet (k + 1) →L[ℝ] Jet k :=
  ContinuousLinearMap.pi fun w => ContinuousLinearMap.proj
    (wordIndex (i :: List.ofFn w.2) (by simp only [List.length_cons, List.length_ofFn]; omega))

theorem restrictJet_finiteJet (k : ℕ) (u : List (Fin d) → Z) :
    restrictJet k (finiteJet (k + 1) u) = finiteJet k u := by
  ext w
  simp only [restrictJet, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply,
    finiteJet, wordIndex_word]

theorem shiftJet_finiteJet (k : ℕ) (i : Fin d) (u : List (Fin d) → Z) :
    shiftJet k i (finiteJet (k + 1) u) = finiteJet k (fun w => u (i :: w)) := by
  ext w
  simp only [shiftJet, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply,
    finiteJet, wordIndex_word]

def sourceStep {k : ℕ} (R : (P × Jet k) → Z) (i : Fin d) : (P × Jet (k + 1)) → Z :=
  fun q => fderiv ℝ R (q.1, restrictJet k q.2) (Pi.single i 1, shiftJet k i q.2)

theorem contDiff_sourceStep {k : ℕ} {R : (P × Jet k) → Z}
    (hR : ContDiff ℝ ∞ R) (i : Fin d) : ContDiff ℝ ∞ (sourceStep R i) := by
  have hder : ContDiff ℝ ∞ (fderiv ℝ R) := (contDiff_infty_iff_fderiv.mp hR).2
  exact (hder.comp (contDiff_fst.prodMk ((restrictJet k).contDiff.comp contDiff_snd))).clm_apply
    (contDiff_const.prodMk ((shiftJet k i).contDiff.comp contDiff_snd))

def prolongedSource {k : ℕ} (R : (P × Jet k) → Z) :
    (w : List (Fin d)) → (P × Jet (k + w.length)) → Z
  | [] => R
  | i :: w => sourceStep (prolongedSource R w) i

theorem contDiff_prolongedSource {k : ℕ} {R : (P × Jet k) → Z}
    (hR : ContDiff ℝ ∞ R) (w : List (Fin d)) :
    ContDiff ℝ ∞ (prolongedSource R w) := by
  induction w with
  | nil => exact hR
  | cons i w ih => exact contDiff_sourceStep ih i


def wordDerivative : List (Fin d) → (P → Z) → P → Z
  | [], f => f
  | i :: w, f => fun p => fderiv ℝ (wordDerivative w f) p (Pi.single i 1)

theorem wordDerivative_contDiffOn {Omega : Set P} (hOmega : IsOpen Omega)
    {f : P → Z} (hf : ContDiffOn ℝ ∞ f Omega) (w : List (Fin d)) :
    ContDiffOn ℝ ∞ (wordDerivative w f) Omega := by
  induction w with
  | nil => exact hf
  | cons i w ih =>
    exact (ih.fderiv_of_isOpen hOmega (by simp)).clm_apply contDiffOn_const

theorem wordDerivative_eventuallyEq {f g : P → Z} {p : P}
    (hfg : f =ᶠ[𝓝 p] g) (w : List (Fin d)) :
    wordDerivative w f =ᶠ[𝓝 p] wordDerivative w g := by
  induction w with
  | nil => exact hfg
  | cons i w ih =>
    exact ih.fderiv.mono (fun q hq => congrArg (fun L : P →L[ℝ] Z => L (Pi.single i 1)) hq)

theorem wordDerivative_add {Omega : Set P} (hOmega : IsOpen Omega)
    {f g : P → Z} (hf : ContDiffOn ℝ ∞ f Omega) (hg : ContDiffOn ℝ ∞ g Omega)
    (w : List (Fin d)) {p : P} (hp : p ∈ Omega) :
    wordDerivative w (fun q => f q + g q) p = wordDerivative w f p + wordDerivative w g p := by
  induction w generalizing p with
  | nil => rfl
  | cons i w ih =>
    have heq : wordDerivative w (fun q => f q + g q) =ᶠ[𝓝 p]
        (fun q => wordDerivative w f q + wordDerivative w g q) := by
      filter_upwards [hOmega.mem_nhds hp] with q hq
      exact ih hq
    have hdf := ((wordDerivative_contDiffOn hOmega hf w).contDiffAt
      (hOmega.mem_nhds hp)).differentiableAt (by simp)
    have hdg := ((wordDerivative_contDiffOn hOmega hg w).contDiffAt
      (hOmega.mem_nhds hp)).differentiableAt (by simp)
    have hd : HasFDerivAt (fun q => wordDerivative w f q + wordDerivative w g q)
        (fderiv ℝ (wordDerivative w f) p + fderiv ℝ (wordDerivative w g) p) p :=
      hdf.hasFDerivAt.add hdg.hasFDerivAt
    change fderiv ℝ _ p (Pi.single i 1) = _
    rw [heq.fderiv_eq, hd.fderiv]
    rfl

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem wordDerivative_clm (L : Z →L[ℝ] Y)
    {Omega : Set P} (hOmega : IsOpen Omega) {f : P → Z}
    (hf : ContDiffOn ℝ ∞ f Omega) (w : List (Fin d)) {p : P} (hp : p ∈ Omega) :
    wordDerivative w (fun q => L (f q)) p = L (wordDerivative w f p) := by
  induction w generalizing p with
  | nil => rfl
  | cons i w ih =>
    have heq : wordDerivative w (fun q => L (f q)) =ᶠ[𝓝 p]
        (fun q => L (wordDerivative w f q)) := by
      filter_upwards [hOmega.mem_nhds hp] with q hq
      exact ih hq
    have hdf := ((wordDerivative_contDiffOn hOmega hf w).contDiffAt
      (hOmega.mem_nhds hp)).differentiableAt (by simp)
    have hd : HasFDerivAt (fun q => L (wordDerivative w f q))
        (L.comp (fderiv ℝ (wordDerivative w f) p)) p :=
      L.hasFDerivAt.comp p hdf.hasFDerivAt
    change fderiv ℝ _ p (Pi.single i 1) = _
    rw [heq.fderiv_eq, hd.fderiv]
    rfl

theorem sourceStep_eq_derivative {k : ℕ} (R : (P × Jet k) → Z)
    (u : List (Fin d) → P → Z) {p : P}
    (hR : DifferentiableAt ℝ R (p, finiteJet k (fun w => u w p)))
    (hu : ∀ w, DifferentiableAt ℝ (u w) p)
    (hshift : ∀ w i, fderiv ℝ (u w) p (Pi.single i 1) = u (i :: w) p)
    (i : Fin d) :
    sourceStep R i (p, finiteJet (k + 1) (fun w => u w p)) =
      fderiv ℝ (fun q => R (q, finiteJet k (fun w => u w q))) p (Pi.single i 1) := by
  let A : P →L[ℝ] Jet k := ContinuousLinearMap.pi
    (fun w => fderiv ℝ (u (List.ofFn w.2)) p)
  have hjet : HasFDerivAt (fun q => finiteJet k (fun w => u w q)) A p :=
    hasFDerivAt_pi.mpr (fun w => (hu (List.ofFn w.2)).hasFDerivAt)
  have hd : HasFDerivAt (fun q => R (q, finiteJet k (fun w => u w q)))
      ((fderiv ℝ R (p, finiteJet k (fun w => u w p))).comp
        ((ContinuousLinearMap.id ℝ P).prod A)) p := by
    simpa only [Function.comp_def, id_eq] using
      hR.hasFDerivAt.comp p ((hasFDerivAt_id p).prodMk hjet)
  rw [hd.fderiv]
  change fderiv ℝ R (p, restrictJet k (finiteJet (k + 1) (fun w => u w p)))
      (Pi.single i 1, shiftJet k i (finiteJet (k + 1) (fun w => u w p))) =
    fderiv ℝ R (p, finiteJet k (fun w => u w p)) (Pi.single i 1, A (Pi.single i 1))
  rw [restrictJet_finiteJet, shiftJet_finiteJet]
  congr 2
  funext w
  exact (hshift (List.ofFn w.2) i).symm


theorem prolongedSource_eq_wordDerivative {k : ℕ} {R : (P × Jet k) → Z}
    (hR : ContDiff ℝ ∞ R) {Omega : Set P} (hOmega : IsOpen Omega)
    (u : List (Fin d) → P → Z)
    (hu : ∀ w p, p ∈ Omega → DifferentiableAt ℝ (u w) p)
    (hshift : ∀ w p, p ∈ Omega → ∀ i,
      fderiv ℝ (u w) p (Pi.single i 1) = u (i :: w) p)
    (w : List (Fin d)) {p : P} (hp : p ∈ Omega) :
    prolongedSource R w (p, finiteJet (k + w.length) (fun a => u a p)) =
      wordDerivative w (fun q => R (q, finiteJet k (fun a => u a q))) p := by
  induction w generalizing p with
  | nil => rfl
  | cons i w ih =>
    have heq :
        (fun q => prolongedSource R w (q, finiteJet (k + w.length) (fun a => u a q)))
          =ᶠ[𝓝 p] wordDerivative w (fun q => R (q, finiteJet k (fun a => u a q))) := by
      filter_upwards [hOmega.mem_nhds hp] with q hq
      exact ih hq
    change sourceStep (prolongedSource R w) i
        (p, finiteJet (k + w.length + 1) (fun a => u a p)) = _
    rw [sourceStep_eq_derivative (prolongedSource R w) u
      ((contDiff_prolongedSource hR w).differentiable (by simp) _)
      (fun a => hu a p hp) (fun a j => hshift a p hp j) i]
    exact congrArg (fun L : P →L[ℝ] Z => L (Pi.single i 1)) heq.fderiv_eq

section PathEquation

variable [CompleteSpace Z] {T : ℝ} (hT : 0 ≤ T)

theorem wordDerivative_integral_equation
    {Omega : Set P} (hOmega : IsOpen Omega)
    (U S : P → C(Icc (0 : ℝ) T, Z)) (initial : P → Z)
    (hS : ContDiffOn ℝ ∞ S Omega) (hinitial : ContDiffOn ℝ ∞ initial Omega)
    (heq : ∀ p ∈ Omega, U p = ContinuousMap.const _ (initial p) + integralOperator hT (S p))
    (w : List (Fin d)) {p : P} (hp : p ∈ Omega) :
    wordDerivative w U p = ContinuousMap.const _ (wordDerivative w initial p) +
      integralOperator hT (wordDerivative w S p) := by
  let C : Z →L[ℝ] C(Icc (0 : ℝ) T, Z) := ContinuousLinearMap.const ℝ _
  have hlocal : U =ᶠ[𝓝 p] (fun q => C (initial q) + integralOperator hT (S q)) := by
    filter_upwards [hOmega.mem_nhds hp] with q hq
    exact heq q hq
  have hci : ContDiffOn ℝ ∞ (fun q => C (initial q)) Omega :=
    C.contDiff.comp_contDiffOn hinitial
  have hjs : ContDiffOn ℝ ∞ (fun q => integralOperator hT (S q)) Omega :=
    (integralOperator (Z := Z) hT).contDiff.comp_contDiffOn hS
  rw [(wordDerivative_eventuallyEq hlocal w).eq_of_nhds,
    wordDerivative_add hOmega hci hjs w hp,
    wordDerivative_clm C hOmega hinitial w hp,
    wordDerivative_clm (integralOperator hT) hOmega hS w hp]
  rfl

theorem wordDerivative_time_derivative
    {Omega : Set P} (hOmega : IsOpen Omega)
    (U S : P → C(Icc (0 : ℝ) T, Z)) (initial : P → Z)
    (hS : ContDiffOn ℝ ∞ S Omega) (hinitial : ContDiffOn ℝ ∞ initial Omega)
    (heq : ∀ p ∈ Omega, U p = ContinuousMap.const _ (initial p) + integralOperator hT (S p))
    (w : List (Fin d)) {p : P} (hp : p ∈ Omega) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => wordDerivative w U p (projIcc 0 T hT s))
      (wordDerivative w S p (projIcc 0 T hT t)) (Icc (0 : ℝ) T) t := by
  have hword := wordDerivative_integral_equation hT hOmega U S initial hS hinitial heq w hp
  have hd := (integralOperator_hasDerivWithinAt hT (wordDerivative w S p) ht).const_add
    (wordDerivative w initial p)
  have hproj : projIcc 0 T hT t = ⟨t, ht⟩ := projIcc_of_mem hT ht
  rw [hproj]
  convert hd using 1
  funext s
  rw [hword]
  rfl

theorem hasFDerivAt_path_word
    {Omega : Set P} (hOmega : IsOpen Omega)
    (U : P → C(Icc (0 : ℝ) T, Z)) (hU : ContDiffOn ℝ ∞ U Omega)
    (w : List (Fin d)) {p : P} (hp : p ∈ Omega) :
    HasFDerivAt (wordDerivative w U)
      (coordinateDifferential (fun i => wordDerivative (i :: w) U p)) p := by
  have hd := ((wordDerivative_contDiffOn hOmega hU w).contDiffAt
    (hOmega.mem_nhds hp)).differentiableAt (by simp)
  have heq : fderiv ℝ (wordDerivative w U) p =
      coordinateDifferential (fun i => wordDerivative (i :: w) U p) := by
    have hlin : (fderiv ℝ (wordDerivative w U) p).toLinearMap =
        (coordinateDifferential (fun i => wordDerivative (i :: w) U p)).toLinearMap := by
      apply (Pi.basisFun ℝ (Fin d)).ext
      intro i
      rw [Pi.basisFun_apply]
      ext t
      change fderiv ℝ (wordDerivative w U) p (Pi.single i 1) t =
        coordinateDifferential (fun j => wordDerivative (j :: w) U p) (Pi.single i 1) t
      rw [coordinateDifferential_apply]
      simp [Pi.single_apply, wordDerivative]
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun L : P →ₗ[ℝ] C(Icc (0 : ℝ) T, Z) => L v) hlin
  rw [← heq]
  exact hd.hasFDerivAt

theorem source_path_word {k : ℕ} {R : (P × Jet k) → Z} (hR : ContDiff ℝ ∞ R)
    {Omega : Set P} (hOmega : IsOpen Omega)
    (U S : P → C(Icc (0 : ℝ) T, Z))
    (hU : ContDiffOn ℝ ∞ U Omega) (hS : ContDiffOn ℝ ∞ S Omega)
    (hsource : ∀ p ∈ Omega, ∀ t : Icc (0 : ℝ) T,
      S p t = R (p, finiteJet k (fun a => wordDerivative a U p t)))
    (w : List (Fin d)) {p : P} (hp : p ∈ Omega) (t : Icc (0 : ℝ) T) :
    wordDerivative w S p t =
      prolongedSource R w (p, finiteJet (k + w.length) (fun a => wordDerivative a U p t)) := by
  let E : C(Icc (0 : ℝ) T, Z) →L[ℝ] Z := ContinuousMap.evalCLM ℝ t
  let u : List (Fin d) → P → Z := fun a q => wordDerivative a U q t
  have hdu (a : List (Fin d)) (q : P) (hq : q ∈ Omega) :
      HasFDerivAt (u a) (E.comp (fderiv ℝ (wordDerivative a U) q)) q :=
    E.hasFDerivAt.comp q (((wordDerivative_contDiffOn hOmega hU a).contDiffAt
      (hOmega.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt
  have hshift (a : List (Fin d)) (q : P) (hq : q ∈ Omega) (i : Fin d) :
      fderiv ℝ (u a) q (Pi.single i 1) = u (i :: a) q := by
    rw [(hdu a q hq).fderiv]
    rfl
  have hlocal : (fun q => S q t) =ᶠ[𝓝 p]
      (fun q => R (q, finiteJet k (fun a => u a q))) := by
    filter_upwards [hOmega.mem_nhds hp] with q hq
    exact hsource q hq t
  calc
    wordDerivative w S p t = wordDerivative w (fun q => S q t) p :=
      (wordDerivative_clm E hOmega hS w hp).symm
    _ = wordDerivative w (fun q => R (q, finiteJet k (fun a => u a q))) p :=
      (wordDerivative_eventuallyEq hlocal w).eq_of_nhds
    _ = _ := (prolongedSource_eq_wordDerivative hR hOmega u
      (fun a q hq => (hdu a q hq).differentiableAt) hshift w hp).symm



theorem joint_smooth_of_integral_finite_jet {k : ℕ} {R : (P × Jet k) → Z}
    (hR : ContDiff ℝ ∞ R) (hTpos : 0 < T)
    {Omega : Set P} (hOmega : IsOpen Omega)
    (U S : P → C(Icc (0 : ℝ) T, Z)) (initial : P → Z)
    (hU : ContDiffOn ℝ ∞ U Omega) (hS : ContDiffOn ℝ ∞ S Omega)
    (hinitial : ContDiffOn ℝ ∞ initial Omega)
    (heq : ∀ p ∈ Omega,
      U p = ContinuousMap.const _ (initial p) + integralOperator hT (S p))
    (hsource : ∀ p ∈ Omega, ∀ t : Icc (0 : ℝ) T,
      S p t = R (p, finiteJet k (fun a => wordDerivative a U p t))) :
    ContDiffOn ℝ ∞ (fun q : ℝ × P => U q.2 (projIcc 0 T hT q.1))
      (Icc (0 : ℝ) T ×ˢ Omega) := by
  have hsystem := contDiffOn_of_spatial_jet_system
    (fun w : List (Fin d) => WordIndex (Fin d) (k + w.length)) hTpos hOmega
    (fun w => wordDerivative w U) (fun w i => i :: w)
    (fun _ j => List.ofFn j.2) (prolongedSource R) (contDiff_prolongedSource hR)
    (fun w p hp => hasFDerivAt_path_word hOmega U hU w hp)
    (fun w p hp t ht => ?_)
  · exact hsystem []
  · change HasDerivWithinAt (fun s => wordDerivative w U p (projIcc 0 T hTpos.le s))
      (prolongedSource R w
        (p, finiteJet (k + w.length) (fun a => wordDerivative a U p (projIcc 0 T hTpos.le t))))
      (Icc (0 : ℝ) T) t
    rw [← source_path_word hR hOmega U S hU hS hsource w hp (projIcc 0 T hTpos.le t)]
    exact wordDerivative_time_derivative hT hOmega U S initial hS hinitial heq w hp ht

end PathEquation

end PoincareConjecture.DeTurckJetProlongationNative

end
