
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro hp,
  intro hnp,
  contradiction,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro hp,
  by_cases h : P,
  apply h,
  contradiction,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  intro hnnp,
  by_cases hp : P,
  apply hp,
  contradiction,
  intro hp,
  intro hnp,
  contradiction,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro hqp,
  cases hqp with hp hq,
  right,
  apply hp,
  left,
  apply hq,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro hpq,
  cases hpq with hp hq,
  split,
  apply hq,
  apply hp,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro hnpq,
  intro hp,
  cases hnpq with hnp hq,
  contradiction,
  apply hq,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro hpq,
  intro hnp,
  cases hpq with hp hq,
  contradiction,
  apply hq,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro hpq,
  intro hnq,
  intro hp,
  have hq : Q := hpq hp,
  contradiction,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro hnqnp,
  intro hp,
  by_cases hlq : Q,
  apply hlq,
  have hnp : ¬P := hnqnp hlq,
  contradiction,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  exact impl_as_contrapositive P Q,
  exact impl_as_contrapositive_converse P Q,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro hnpp,
  apply hnpp,
  right,
  intro hp,
  apply hnpp,
  left,
  apply hp,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intros hpqp hp,
  by_cases hlp : P,
  contradiction,
  apply hlp,

end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intros hpq hnpq,
  cases hpq with hp hq,
  cases hnpq,
  contradiction,
  cases hnpq,
  contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intros hpq hnpq,
  cases hnpq with hp hq,
  cases hpq,
  contradiction,
  cases hpq,
  contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro hnpq,
  split,
  intro hp,
  apply hnpq,
  left,
  apply hp,
  intro hq,
  apply hnpq,
  right,
  apply hq,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intros hnpnq hpq,
  cases hpq with hp hq,
  cases hnpnq,
    contradiction,
  cases hnpnq,
    contradiction,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
 intro hnpq,
  by_cases hlq: Q,
    --- lem Q
    right,
    intro hp,
    have himpl_pq : P∧Q,
      split,
      exact hp,
      exact hlq,
    apply hnpq,
    exact himpl_pq,
    left,
    exact hlq,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intros hnqnp hpq,
  cases hpq,
  cases hnqnp,
    -- case ¬Q
    contradiction,
    -- Case ¬P
    contradiction,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  exact demorgan_conj P Q,
  exact demorgan_conj_converse P Q,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  exact demorgan_disj P Q,
  exact demorgan_disj_converse P Q,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro hp_and_qr,
  cases hp_and_qr,
  cases hp_and_qr_right with hq hr,
  left,
  split,
  assumption',
  right,
  split,
  assumption',
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro hpq_or_pr,
  cases hpq_or_pr with hpq hpr,
  split,
  cases hpq,
  assumption,
  cases hpq,
  left,
  assumption,
  split,
  cases hpr,
  assumption,
  cases hpr,
  right,
  assumption,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro hpqr,
  -- split,
  cases hpqr,
  split,
  left,
  assumption,
  left,
  assumption,
  cases hpqr,
  split,
  right,
  assumption,
  right,
  assumption,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro hpq_pr,
  cases hpq_pr,
  cases hpq_pr_left,
  left,
  assumption,
  cases hpq_pr_right,
  left,
  assumption,
  right,
  split,
  assumption',
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intros hpq_impl_r hp hq,
  apply hpq_impl_r,
  split,
  assumption',
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intros hp_q_r hpq,
  cases hpq,
  apply hp_q_r,
  assumption',
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro hp,
  assumption,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro hp,
  left,
  exact hp,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro hq,
  right,
  exact hq,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro hpq,
  cases hpq,
  exact hpq_left,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro hpq,
  cases hpq,
  exact hpq_right,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro hpp,
  cases hpp,
  assumption,
  intro hp,
  split,
  assumption,
  assumption,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro hp_or_p,
  cases hp_or_p,
  assumption,
  assumption,
  intro hp,
  left,
  assumption,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro hn_e_p,
  intros x hxp,
  apply hn_e_p,
  existsi x,
  assumption,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro htqx,
  intro hex,
  cases hex with x hpx,
  exact htqx x hpx,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro hnptx,
  
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro hexnp,
  intro htx,
  cases hexnp with hx hnp,
  -- htx x,
end 

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  sorry,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  sorry,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
