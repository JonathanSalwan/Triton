#ifndef TRITON_ASTCONTEXT_HPP
#define TRITON_ASTCONTEXT_HPP

#include <triton/symbolicExpression.hpp>

#include <tritonast/context.hpp>

#include <unordered_map>

namespace triton {

// Note: Find a better name
class AstContext: public triton::ast::Context
{
    public:
        AstContext() = default;

        AstContext& operator=(AstContext const&) = delete;
        AstContext& operator=(AstContext &&) = default;
        ~AstContext() = default;

        triton::ast::SharedAbstractNode reference(triton::SharedSymbolicExpression const& se)
        {
            int id = se->getId();
            auto it = this->refs_.find(id);
            if(it != this->refs_.end()) {
                auto sp = it->second.lock();
                if(sp)
                    return sp;
            }

            // Here we use the lambda context capture to increase the reference counter
            // the context destruction with lambda destructor to release the reference
            // counter on se.
            auto sp = triton::ast::Context::reference(se->getShareAst(), id, [se](){});
            this->refs_[id] = sp;
            return sp;
        }

    private:
        std::unordered_map<triton::usize, std::weak_ptr<triton::ast::AbstractNode>> refs_;
};

}

#endif
