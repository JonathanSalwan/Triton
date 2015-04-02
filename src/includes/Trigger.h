#ifndef _TRIGGER_H_
#define _TRIGGER_H_

class Trigger {
  public:
    // Build a trigger set in the OFF state.
    Trigger();

    // Switch the trigger.
    void toggle();

    // Return true if the switch is ON, false otherwise.
    bool getState();

    // Set this->state to true
    void enable(void);

    // Set this->state to false
    void disable(void);

    // Set this->state to flag
    void update(bool flag);

  private:
    bool state;
};

#endif // _TRIGGER_H_
