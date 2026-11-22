#ifndef L4YAML_RAII_HPP
#define L4YAML_RAII_HPP

#include "l4yaml.h"
#include <utility>  // for std::move

namespace l4yaml {

/**
 * RAII wrapper for L4YAML opaque handles.
 * Automatically calls l4yaml_free() on destruction.
 *
 * Example usage:
 *   L4YAMLHandle<l4yaml_value_t> value(l4yaml_value_lookup(parent, "key"));
 *   if (value) {
 *     const char* str = l4yaml_value_string(value.get());
 *   }
 *   // Automatic cleanup when value goes out of scope
 */
template<typename T>
class L4YAMLHandle {
public:
    // Constructor from raw handle
    explicit L4YAMLHandle(T handle = nullptr) : handle_(handle) {}

    // Destructor - automatically frees the handle
    ~L4YAMLHandle() {
        if (handle_) {
            l4yaml_free(handle_);
        }
    }

    // Delete copy constructor and copy assignment (prevent double-free)
    L4YAMLHandle(const L4YAMLHandle&) = delete;
    L4YAMLHandle& operator=(const L4YAMLHandle&) = delete;

    // Move constructor
    L4YAMLHandle(L4YAMLHandle&& other) noexcept : handle_(other.handle_) {
        other.handle_ = nullptr;
    }

    // Move assignment
    L4YAMLHandle& operator=(L4YAMLHandle&& other) noexcept {
        if (this != &other) {
            if (handle_) {
                l4yaml_free(handle_);
            }
            handle_ = other.handle_;
            other.handle_ = nullptr;
        }
        return *this;
    }

    // Get the raw handle
    T get() const { return handle_; }

    // Release ownership (returns raw handle without freeing)
    T release() {
        T tmp = handle_;
        handle_ = nullptr;
        return tmp;
    }

    // Reset to a new handle (frees old handle if present)
    void reset(T handle = nullptr) {
        if (handle_) {
            l4yaml_free(handle_);
        }
        handle_ = handle;
    }

    // Boolean conversion (check if handle is non-null)
    explicit operator bool() const { return handle_ != nullptr; }

    // Implicit conversion to raw handle for C API calls
    operator T() const { return handle_; }

private:
    T handle_;
};

// Type aliases for common handle types
using ResultHandle = L4YAMLHandle<l4yaml_result_t>;
using ValueHandle = L4YAMLHandle<l4yaml_value_t>;
using DocsHandle = L4YAMLHandle<l4yaml_docs_t>;
using DocHandle = L4YAMLHandle<l4yaml_doc_t>;

} // namespace l4yaml

#endif // L4YAML_RAII_HPP
