require 'matrix'

class ViterbiHMM
  attr_reader :transition, :emission, :initial_probs

  def initialize(trans, emis, init)
    @transition = Matrix[*trans]
    @emission = Matrix[*emis]
    @initial_probs = init
  end

  def viterbi(observations)
    a = (0...observations.length).map { Array.new num_states }

    # a[0][x_0] = p(y0,x_0) = p(y_0|x_0)p(x_0)
    a[0] = (0...num_states).map do |state|
      path = [state]
      prob = emission[state, observations[0]] * initial_probs[state]
      [path, prob]
    end

    # Suppose 12232325 is the most likely sequence of states for the 8 observations.
    # Then 1223232 must be the most likely sequence of states for the first 7
    # observations that ends in 2, or else we could have used that one instead.
    # This suggests we can find the most likely sequence of n states by
    # computing, for each state k, the most likely sequence of n-1 states
    # that end in state k.
    # a[k][x_i] = most likely sequence p(y_0, ..., y_k, x_0, ..., x_k) with x_k = x_i
    # = max_j p(y_k|x_k)p(x_k|x_k-1=x_j)a[k-1][x_j]
    (1...observations.length).each do |k|
      (0...num_states).each do |state|
        max_prob = nil
        max_path = nil
        a[k-1].each do |(path, prob)|
          prev_state = path.last
          new_path = path + [state]
          t = transition[prev_state, state]
          e = emission[state, observations[k]]
          new_prob = t * e * prob

          max_prob ||= new_prob
          max_path ||= new_path

          if new_prob > max_prob
            max_prob = new_prob
            max_path = new_path
          end
        end

        a[k][state] = [max_path, max_prob]
      end
    end

    a[observations.length - 1].max_by {|x| x[1] }
  end

  def num_states
    initial_probs.length
  end
end

transition_rows = [[0.99, 0.01],
                   [0.1, 0.9]]

p = 1/6.to_f
emission_rows = [[p, p, p, p, p, p],
                 [p/5, p/5, p/5, p/5, p/5, 5*p]]
init = [0.5, 0.5]
hmm = ViterbiHMM.new(transition_rows, emission_rows, init)
require 'pry'
binding.pry
